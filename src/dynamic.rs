use std::{
    cell::RefCell,
    collections::BTreeMap,
    ops::{Index, IndexMut},
    rc::Rc,
};

use move_model::model::QualifiedInstId;
use move_stackless_bytecode::stackless_bytecode::{
    AbortAction, AssignKind, Bytecode, Constant, Label, Operation, BorrowNode, BorrowEdge,
};
use symbolic_evaluation::traits::Transition;
use z3::{ast::Ast, Context};

use crate::{
    constraint::{Constrained, Disjoints},
    state::{
        BranchCondition, CodeOffset, GlobalState, LocalState, MoveState, TempIndex,
        TerminationStatus,
    },
    ty::{new_resource_id, Datatypes},
    value::{ConstrainedValue, PrimitiveValue, Value, Loc},
};

// Evaluate an `Assign`.
fn assign<'ctx>(
    dst: TempIndex,
    src: TempIndex,
    kind: &AssignKind,
    mut s: LocalState<'ctx>,
) -> LocalState<'ctx> {
    let src_val = match kind {
        AssignKind::Move => s.del(src),
        AssignKind::Copy | AssignKind::Store => s.index(src).content.clone(),
    };
    s.index_mut(dst).content = src_val;
    s.ic += 1;
    s
}

// Evaluate a `Load`.
fn load<'ctx>(dst: TempIndex, c: &Constant, mut s: LocalState<'ctx>) -> LocalState<'ctx> {
    s[dst].content = Disjoints(vec![ConstrainedValue::new(
        Value::from_constant(c, s.get_ctx()),
        s.pc.clone(),
    )]);
    s.ic += 1;
    s
}

// Evaluate a `Jump`.
fn jump<'ctx>(
    label: &Label,
    label_to_offset: &BTreeMap<Label, CodeOffset>,
    s: LocalState<'ctx>,
) -> LocalState<'ctx> {
    LocalState {
        ic: *label_to_offset.get(label).unwrap(),
        ..s
    }
}

// Evaluate a `Branch`.
fn branch<'ctx>(
    ctx: &'ctx Context,
    label_to_offset: &BTreeMap<Label, CodeOffset>,
    cond: TempIndex,
    then_label: &Label,
    else_label: &Label,
    s: LocalState<'ctx>,
) -> Vec<LocalState<'ctx>> {
    let BranchCondition {
        true_branch,
        false_branch,
    } = s.index(cond).to_branch_condition(ctx).expect(&format!(
        "${}, used as a branch condition, is not of boolean type.",
        cond
    ));
    vec![
        jump(then_label, label_to_offset, s.clone() & true_branch),
        jump(else_label, label_to_offset, s & false_branch),
    ]
}

// Handle pure operations.
// the arity of inputs is checked in `op`
fn pure_local_operation<'ctx, F>(
    dsts: &[TempIndex],
    op: F,
    srcs: &[TempIndex],
    mut s: LocalState<'ctx>,
) -> LocalState<'ctx>
where
    F: Fn(Vec<Value<'ctx>>) -> Vec<Value<'ctx>> + Clone,
{
    let constrained_args = s.args(srcs);
    let res = constrained_args.map(op);
    for &x in dsts {
        s.index_mut(x).del();
    }
    for Constrained {
        content: vals,
        constraint,
    } in res
    {
        debug_assert!(vals.len() == dsts.len());
        for (&x, val) in dsts.iter().zip(vals.into_iter()) {
            s.index_mut(x)
                .content
                .0
                .push(ConstrainedValue::new(val.simplify(), constraint.clone()))
        }
    }
    s
}

fn pure_local_operation_<'ctx, F>(
    dsts: &[TempIndex],
    op: F,
    srcs: &[TempIndex],
    s: LocalState<'ctx>,
    t: GlobalState<'ctx>,
) -> Vec<(LocalState<'ctx>, GlobalState<'ctx>)>
where
    F: Fn(Vec<Value<'ctx>>) -> Vec<Value<'ctx>> + Clone,
{
    vec![(pure_local_operation(dsts, op, srcs, s), t)]
}

fn operation<'ctx, 'env>(
    dsts: &[TempIndex],
    op: &Operation,
    srcs: &[TempIndex],
    _on_abort: Option<&AbortAction>,
    mut s: LocalState<'ctx>,
    mut t: GlobalState<'ctx>,
    datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
) -> Vec<(LocalState<'ctx>, GlobalState<'ctx>)> {
    use Operation::*;
    s.ic += 1;
    match op {
        // Pack(ModuleId, StructId, Vec<Type>),
        Pack(module_id, struct_id, type_params) => pure_local_operation_(
            dsts,
            |x: Vec<Value>| {
                let resource_type = QualifiedInstId {
                    module_id: *module_id,
                    inst: type_params.clone(),
                    id: *struct_id,
                };
                let mut dt = datatypes.borrow_mut();
                let struct_type = dt.from_struct(&resource_type);
                vec![Value::Struct(
                    struct_type.variants[0]
                        .constructor
                        .apply(
                            x.iter()
                                .map(|x| x.unwrap())
                                .collect::<Vec<&dyn Ast>>()
                                .as_slice(),
                        )
                        .as_datatype()
                        .unwrap()
                        .simplify(),
                )]
            },
            srcs,
            s,
            t,
        ),
        // Unpack(ModuleId, StructId, Vec<Type>),
        Unpack(module_id, struct_id, type_params) => pure_local_operation_(
            dsts,
            |x: Vec<Value>| {
                let resource_type = QualifiedInstId {
                    module_id: *module_id,
                    inst: type_params.clone(),
                    id: *struct_id,
                };
                let field_types = datatypes.borrow().get_field_types(*module_id, *struct_id);
                let mut dt = datatypes.borrow_mut();
                let struct_sort = dt.from_struct(&resource_type);
                struct_sort.variants[0]
                    .accessors
                    .iter()
                    .zip(field_types.iter())
                    .map(|(f, t)| Value::wrap(&f.apply(&[x[0].unwrap()]).simplify(), &t))
                    .collect()
            },
            srcs,
            s,
            t,
        ),

        // Resources
        MoveTo(module_id, struct_id, type_params) => {
            let addr_val = s[srcs[0]].content.clone();
            let resource_type = QualifiedInstId {
                module_id: *module_id,
                inst: type_params.clone(),
                id: *struct_id,
            };
            let branch_condition = t
                .exists(&resource_type, &addr_val)
                .to_branch_condition(s.get_ctx());
            let mut true_branch_local_state = s.clone() & branch_condition.true_branch.clone();
            true_branch_local_state.ts = TerminationStatus::Abort(Disjoints(vec![]));
            let true_branch_global_state = t.clone() & branch_condition.true_branch;
            let false_branch_local_state = s & branch_condition.false_branch.clone();
            let mut false_branch_global_state = t.clone() & branch_condition.false_branch;
            false_branch_global_state.real_move_to(
                &resource_type,
                &false_branch_local_state[srcs[0]]
                    .content
                    .clone()
                    .map(|x| x.as_addr().unwrap().clone()),
                false_branch_local_state[srcs[1]]
                    .content
                    .clone()
                    .map(|x| x.as_datatype().unwrap().clone()),
                datatypes,
            );
            vec![
                (true_branch_local_state, true_branch_global_state),
                (false_branch_local_state, false_branch_global_state),
            ]
        }
        MoveFrom(module_id, struct_id, type_params) => {
            let addr_val = s[srcs[0]].content.clone();
            let resource_id = new_resource_id(*module_id, *struct_id, type_params.clone());
            let branch_condition = t
                .exists(&resource_id, &addr_val)
                .to_branch_condition(s.get_ctx());
            let mut true_branch_local_state = s.clone() & branch_condition.true_branch.clone();
            let mut true_branch_global_state = t.clone() & branch_condition.true_branch;
            let resource_moved_out = true_branch_global_state.real_move_from(
                &resource_id,
                &true_branch_local_state[srcs[0]]
                    .content
                    .clone()
                    .map(|x| x.as_addr().unwrap().clone()),
                datatypes,
            );
            true_branch_local_state[dsts[0]].content =
                resource_moved_out.map(|x| Value::Struct(x.as_datatype().unwrap()));
            let mut false_branch_local_state = s & branch_condition.false_branch.clone();
            false_branch_local_state.ts = TerminationStatus::Abort(Disjoints(vec![]));
            let false_branch_global_state = t.clone() & branch_condition.false_branch;
            vec![
                (true_branch_local_state, true_branch_global_state),
                (false_branch_local_state, false_branch_global_state),
            ]
        }
        Exists(module_id, struct_id, type_params) => {
            let dst = dsts[0];
            let src = srcs[0];
            let src_val = s[src].content.clone();
            let resource_type = QualifiedInstId {
                module_id: *module_id,
                inst: type_params.clone(),
                id: *struct_id,
            };
            s[dst].content = t
                .exists(&resource_type, &src_val)
                .map(|x| Value::Primitive(PrimitiveValue::Bool(x)));
            vec![(s, t)]
        }

        // Borrow
        // BorrowLoc,
        BorrowLoc => {
          let src = srcs[0];
          let src_val = s[src].content.clone();
          s[dsts[0]].content = src_val.map(
            |v| Value::Reference(
              Box::new(v),
              Some(
                Loc(BorrowNode::LocalRoot(src), BorrowEdge::Direct)
              )
            )
          );
          vec![(s, t)]
        }
        // BorrowField(ModuleId, StructId, Vec<Type>, usize),
        BorrowField(module_id, struct_id, type_params, field_id) => {
          pure_local_operation_(
            dsts,
            |x| {
              assert_eq!(x.len(), 1);
              let resource_type = new_resource_id(*module_id, *struct_id, type_params.clone());
              let field_types = datatypes.borrow().get_field_types(*module_id, *struct_id);
              let mut dt = datatypes.borrow_mut();
              let struct_sort = dt.from_struct(&resource_type);
              let field_accessor = &struct_sort.variants[0]
                  .accessors[*field_id];
              let field_val = field_accessor.apply(&[x[0].unwrap()]);
              vec![
                Value::Reference(
                  Box::new(Value::wrap(&field_val, &field_types[*field_id])),
                  Some(Loc(BorrowNode::Reference(srcs[0]), BorrowEdge::Field(resource_type, *field_id)))
                )
              ]
            },
            srcs,
            s,
            t
          )
        }
        // BorrowGlobal(ModuleId, StructId, Vec<Type>),
        BorrowGlobal(module_id, struct_id, type_params) => {
          let addr_val = s[srcs[0]].content.clone();
          let resource_id = new_resource_id(*module_id, *struct_id, type_params.clone());
          let branch_condition = t
              .exists(&resource_id, &addr_val)
              .to_branch_condition(s.get_ctx());
          let mut true_branch_local_state = s.clone() & branch_condition.true_branch.clone();
          let mut true_branch_global_state = t.clone() & branch_condition.true_branch;
          let addr_to_resource = true_branch_global_state.get_resource_value(&resource_id, datatypes);
          let addr = true_branch_local_state[srcs[0]].content.clone().map(|x| x.as_addr().unwrap().clone());
          let resource = addr_to_resource.prod(&addr).map(
            |(array, addr)| Value::Struct(array.select(&addr).as_datatype().unwrap())
          );
          let resouce_ref = resource.map(
            |x| Value::Reference(
              Box::new(x),
              Some(Loc(BorrowNode::GlobalRoot(resource_id.clone()), BorrowEdge::Direct)),
            )
          );
          true_branch_local_state[dsts[0]].content = resouce_ref;
          let mut false_branch_local_state = s & branch_condition.false_branch.clone();
          false_branch_local_state.ts = TerminationStatus::Abort(Disjoints(vec![]));
          let false_branch_global_state = t.clone() & branch_condition.false_branch;
          vec![
              (true_branch_local_state, true_branch_global_state),
              (false_branch_local_state, false_branch_global_state),
          ]
        }

        // Unary
        // CastU8 => todo!
        // CastU64 => todo!
        // CastU128 => todo!
        Not => pure_local_operation_(
            dsts,
            |x: Vec<Value>| {
                assert_eq!(x.len(), 1);
                vec![!x.index(0)]
            },
            srcs,
            s,
            t,
        ),
        // Binary
        Add => pure_local_operation_(
            dsts,
            |x: Vec<Value>| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) + x.index(1)]
            },
            srcs,
            s,
            t,
        ),
        Sub => pure_local_operation_(
            dsts,
            |x: Vec<Value>| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) - x.index(1)]
            },
            srcs,
            s,
            t,
        ),
        Mul => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) * x.index(1)]
            },
            srcs,
            s,
            t,
        ),
        Div => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) / x.index(1)]
            },
            srcs,
            s,
            t,
        ),
        Mod => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) % x.index(1)]
            },
            srcs,
            s,
            t,
        ),
        BitOr => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) | x.index(1)]
            },
            srcs,
            s,
            t,
        ),
        BitAnd => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) & x.index(1)]
            },
            srcs,
            s,
            t,
        ),
        Xor => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) ^ x.index(1)]
            },
            srcs,
            s,
            t,
        ),
        // Shl,
        // Shr,
        Lt => pure_local_operation_(
            dsts,
            |x| {
                println!("fjdkf");
                assert_eq!(x.len(), 2);
                vec![x[0].lt(&x[1])]
            },
            srcs,
            s,
            t,
        ),
        Gt => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].gt(&x[1])]
            },
            srcs,
            s,
            t,
        ),
        Le => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].le(&x[1])]
            },
            srcs,
            s,
            t,
        ),
        Ge => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].ge(&x[1])]
            },
            srcs,
            s,
            t,
        ),
        Or => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].or(&x[1])]
            },
            srcs,
            s,
            t,
        ),
        And => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].and(&x[1])]
            },
            srcs,
            s,
            t,
        ),
        Eq => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].eq(&x[1])]
            },
            srcs,
            s,
            t,
        ),
        Neq => pure_local_operation_(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].neq(&x[1])]
            },
            srcs,
            s,
            t,
        ),
        // CastU256,
        _ => vec![(s, t)],
    }
}

pub fn step<'ctx, 'env>(
    mut s: MoveState<'ctx, 'env>,
    instr: &Bytecode,
    datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
) -> Vec<MoveState<'ctx, 'env>> {
    match instr {
        Bytecode::Assign(_, dst, src, kind) => vec![MoveState {
            local_state: assign(*dst, *src, kind, s.local_state),
            ..s
        }],
        Bytecode::Call(_, dsts, op, srcs, on_abort) => {
            let res = operation(
                dsts,
                op,
                srcs,
                on_abort.as_ref(),
                s.local_state.clone(),
                s.global_state.clone(),
                datatypes,
            );
            res.into_iter()
                .map(|(local_state, global_state)| MoveState {
                    local_state,
                    global_state,
                    ..s.clone()
                })
                .collect()
        }
        Bytecode::Ret(_, srcs) => vec![{
            s.local_state.ts = TerminationStatus::Return(
                srcs.iter()
                    .map(|&x| s.local_state[x].content.clone())
                    .collect(),
            );
            s
        }],
        Bytecode::Load(_, dst, c) => vec![MoveState {
            local_state: load(*dst, c, s.local_state),
            ..s
        }],
        Bytecode::Label(_, _) => {
            s.local_state.ic += 1;
            vec![s]
        }
        Bytecode::Jump(_, label) => vec![MoveState {
            local_state: jump(label, &s.label_to_offset, s.local_state),
            ..s
        }],
        Bytecode::Branch(_, then_label, else_label, cond) => {
            let label_to_offset = &s.label_to_offset;
            branch(
                s.local_state.get_ctx(),
                label_to_offset,
                *cond,
                then_label,
                else_label,
                s.local_state.clone(),
            )
            .into_iter()
            .map(|local_state| MoveState {
                local_state,
                ..s.clone()
            })
            .collect()
        }
        Bytecode::Abort(_, index) => {
            s.local_state.ts = TerminationStatus::Abort(s.local_state[*index].content.clone());
            vec![s]
        }
        _ => {
            s.local_state.ic += 1;
            vec![s]
        }
    }
}

impl<'ctx, 'env> Transition for MoveState<'ctx, 'env> {
    type IntoIter = Vec<MoveState<'ctx, 'env>>;

    fn suc(self) -> Vec<MoveState<'ctx, 'env>> {
        assert!(!self.is_final());
        let instr = self.cur_instr().clone();
        let datatypes = self.datatypes.clone();
        step(self, &instr, datatypes)
    }

    fn is_final(&self) -> bool {
        self.get_local_state().ic() >= self.bytecodes.len() as u16
            || self.get_local_state().termination_status().is_final()
    }
}
