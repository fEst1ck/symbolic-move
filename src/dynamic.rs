use std::{
    cell::RefCell,
    collections::BTreeMap,
    ops::{Index, IndexMut},
    rc::Rc,
};

use move_model::model::QualifiedInstId;
use move_stackless_bytecode::stackless_bytecode::{
    AbortAction, AssignKind, Bytecode, Constant, Label, Operation,
};
use symbolic_evaluation::traits::Transition;
use z3::{
    ast::{Ast, Dynamic},
    Context, FuncDecl,
};

use crate::{locals, 
    constraint::{Constrained, Constraint, Disjoints},
    state::{
        BranchCondition, CodeOffset, GlobalState, Local, LocalState, MoveState, TempIndex,
        TerminationStatus,
    },
    ty::{new_resource_id, Datatypes, FieldId, Type},
    value::{ConstrainedValue, Loc, PrimitiveValue, Root, Value},
};

mod local {
    use super::*;
    // Evaluate an `Assign`.
    fn assign<'ctx>(dst: TempIndex, src: TempIndex, kind: &AssignKind, s: &mut LocalState<'ctx>) {
        let src_val = match kind {
            AssignKind::Move => s.del(src),
            AssignKind::Copy | AssignKind::Store => s.index(src).content.clone(),
        };
        s.index_mut(dst).content = src_val;
        s.ic += 1;
    }

    // Evaluate a `Load`.
    fn load<'ctx>(dst: TempIndex, c: &Constant, s: &mut LocalState<'ctx>) {
        s[dst].content = Disjoints(vec![ConstrainedValue::new(
            Value::from_constant(c, s.get_ctx()),
            s.pc.clone(),
        )]);
        s.ic += 1;
    }

    // Handle pure operations.
    // the arity of inputs is checked in `op`
    fn pure_local_operation<'ctx, F>(
        dsts: &[TempIndex],
        op: F,
        srcs: &[TempIndex],
        s: &mut LocalState<'ctx>,
    ) where
        F: Fn(Vec<Value<'ctx>>) -> Vec<Value<'ctx>> + Clone,
    {
        let constrained_args = s.args(srcs);
        let dests_val = constrained_args.map(op);
        for &x in dsts {
            s.index_mut(x).del();
        }
        for Constrained {
            content: vals,
            constraint,
        } in dests_val
        {
            debug_assert!(vals.len() == dsts.len());
            for (&dst, val) in dsts.iter().zip(vals.into_iter()) {
                s.index_mut(dst)
                    .content
                    .0
                    .push(ConstrainedValue::new(val.simplify(), constraint.clone()))
            }
        }
    }

    // executes operation on `s`, `t` and return abort condition
    fn operation<'ctx, 'env>(
        dsts: &[TempIndex],
        op: &Operation,
        srcs: &[TempIndex],
        _on_abort: Option<&AbortAction>,
        s: &mut LocalState<'ctx>,
        t: &mut GlobalState<'ctx>,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
    ) -> Option<Constraint<'ctx>> {
        fn access_path_tys<'ctx, 'env, 'a, 'b>(
            mut root_type: Type,
            access_path: &[usize],
            datatype: &'a mut Datatypes<'ctx, 'env>,
        ) {
            for &edge in access_path {
                match root_type {
                    Type::Struct(module_id, struct_id, type_params) => {
                        datatype.insert(module_id, struct_id, type_params.clone());
                        let field_types = Type::instantiate_vec(
                            datatype.get_field_types(module_id, struct_id),
                            &type_params,
                        );
                        root_type = field_types[edge].clone();
                    }
                    _ => unreachable!(),
                }
            }
        }

        // Type of the value at `root`
        fn root_type<'ctx, 'env>(
            s: &LocalState<'ctx>,
            root: Root<'ctx>,
            datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
        ) -> Type {
            match root {
                Root::Global(resource_id, _) => datatypes.borrow().get_resource_type(resource_id),
                Root::Local(local_index) => s[local_index].ty.clone(),
            }
        }

        // Return value at `root`
        fn read_ref_root<'env, 'ctx>(
            s: &LocalState<'ctx>,
            mut t: GlobalState<'ctx>,
            root: Root<'ctx>,
            datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
        ) -> Disjoints<'ctx, Value<'ctx>> {
            match root {
                Root::Global(resource_id, addr) => t
                    .get_resource_value(&resource_id, datatypes)
                    .map(|addr_to_resource_val| {
                        Value::Struct(addr_to_resource_val.select(&addr).as_datatype().unwrap())
                    }),
                Root::Local(local_index) => s[local_index].content.clone(),
            }
        }

        // Return value at `loc`
        fn read_ref<'env, 'ctx>(
            s: &LocalState<'ctx>,
            t: GlobalState<'ctx>,
            loc: Loc<'ctx>,
            root_type: &Type,
            datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
        ) -> Disjoints<'ctx, Dynamic<'ctx>> {
            // accessors = f, g, ...
            // out: (... (g (f v)) ...)
            fn rep_select<'ctx>(v: Dynamic<'ctx>, accessors: &[&FuncDecl<'ctx>]) -> Dynamic<'ctx> {
                accessors
                    .iter()
                    .fold(v, |acc, accessor| accessor.apply(&[&acc]).simplify())
            }
            fn accessors_along_path<'ctx, 'env, 'a>(
                mut root_type: Type,
                access_path: &[usize],
                datatype: &'a mut Datatypes<'ctx, 'env>,
            ) -> Option<Vec<&'a FuncDecl<'ctx>>> {
                access_path_tys(root_type.clone(), access_path, datatype);
                let mut res = Vec::new();
                for &edge in access_path {
                    match root_type.clone() {
                        Type::Struct(mod_id, struct_id, type_params) => {
                            let accessor = datatype.unpack(&root_type).unwrap().index(edge);
                            res.push(accessor);
                            let field_types = Type::instantiate_vec(
                                datatype.get_field_types(mod_id, struct_id),
                                &type_params,
                            );
                            root_type = field_types[edge].clone();
                        }
                        _ => return None,
                    }
                }
                Some(res)
            }
            let Loc { root, access_path } = loc;
            let root_val =
                read_ref_root(s, t, root.clone(), datatypes.clone()).map(|x| x.as_dynamic());
            let datatypes_borrow = &mut datatypes.borrow_mut();
            let accessors =
                accessors_along_path(root_type.clone(), &access_path, datatypes_borrow).unwrap();
            root_val.map(|x| rep_select(x, &accessors[..]))
        }

        // Handle pure operations.
        // the arity of inputs is checked in `op`
        fn pure_local_operation<'ctx, F>(
            dsts: &[TempIndex],
            op: F,
            srcs: &[TempIndex],
            s: &mut LocalState<'ctx>,
        ) -> Option<Constraint<'ctx>>
        where
            F: Fn(Vec<Value<'ctx>>) -> Vec<Value<'ctx>> + Clone,
        {
            super::local::pure_local_operation(dsts, op, srcs, s);
            None
        }

        use Operation::*;
        s.ic += 1;
        match op {
            // Pack(ModuleId, StructId, Vec<Type>),
            Pack(module_id, struct_id, type_params) => pure_local_operation(
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
            ),
            // Unpack(ModuleId, StructId, Vec<Type>),
            Unpack(module_id, struct_id, type_params) => pure_local_operation(
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
                *s &= branch_condition.false_branch.clone();
                *t &= branch_condition.false_branch;
                t.real_move_to(
                    &resource_type,
                    &s[srcs[0]]
                        .content
                        .clone()
                        .map(|x| x.as_addr().unwrap().clone()),
                    s[srcs[1]]
                        .content
                        .clone()
                        .map(|x| x.as_datatype().unwrap().clone()),
                    datatypes,
                );
                Some(branch_condition.true_branch)
            }
            MoveFrom(module_id, struct_id, type_params) => {
                let addr_val = s[srcs[0]].content.clone();
                let resource_id = new_resource_id(*module_id, *struct_id, type_params.clone());
                let branch_condition = t
                    .exists(&resource_id, &addr_val)
                    .to_branch_condition(s.get_ctx());
                *s &= branch_condition.true_branch.clone();
                *t &= branch_condition.true_branch;
                let resource_moved_out = t.real_move_from(
                    &resource_id,
                    &s[srcs[0]]
                        .content
                        .clone()
                        .map(|x| x.as_addr().unwrap().clone()),
                    datatypes,
                );
                s[dsts[0]].content =
                    resource_moved_out.map(|x| Value::Struct(x.as_datatype().unwrap()));
                Some(branch_condition.false_branch)
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
                None
            }

            // Borrow
            // BorrowLoc,
            BorrowLoc => {
                s[dsts[0]].content = Disjoints(vec![Constrained::new(
                    Value::Reference(Loc {
                        root: Root::Local(srcs[0]),
                        access_path: Vec::new(),
                    }),
                    s.pc.clone(),
                )]);
                None
            }
            // BorrowField(ModuleId, StructId, Vec<Type>, usize),
            BorrowField(_, _, _, field_id) => {
                s[dsts[0]].content = s[srcs[0]].content.clone().map(|x| match x {
                    Value::Reference(Loc { root, access_path }) => {
                        let mut new_access_path = access_path;
                        new_access_path.push(*field_id);
                        Value::Reference(Loc {
                            root,
                            access_path: new_access_path,
                        })
                    }
                    _ => unreachable!(),
                });
                None
            }
            // BorrowGlobal(ModuleId, StructId, Vec<Type>),
            BorrowGlobal(module_id, struct_id, type_params) => {
                s[dsts[0]].content = s[srcs[0]].content.clone().map(|x| {
                    Value::Reference(Loc {
                        root: Root::Global(
                            new_resource_id(*module_id, *struct_id, type_params.clone()),
                            x.as_addr().unwrap().clone(),
                        ),
                        access_path: Vec::new(),
                    })
                });
                None
            }
            // Get
            GetField(mod_id, struct_id, type_params, field_num) => {
                let mut datatypes_mut = datatypes.borrow_mut();
                let (_, accessors) = datatypes_mut
                    .pack_unpack(&Type::Struct(*mod_id, *struct_id, type_params.clone()))
                    .unwrap();
                let accessor = &accessors[*field_num];
                let dst_type = &s[dsts[0]].ty;
                s[dsts[0]].content = s[srcs[0]].content.clone().map(|x| {
                    let unwrapped_res = accessor.apply(&[&x.as_dynamic()]).simplify();
                    Value::wrap(&unwrapped_res, dst_type)
                });
                None
            }
            GetGlobal(mod_id, struct_id, type_params) => {
                let addr_val = s[srcs[0]].content.clone();
                let resource_id = new_resource_id(*mod_id, *struct_id, type_params.clone());
                let branch_condition = t
                    .exists(&resource_id, &addr_val)
                    .to_branch_condition(s.get_ctx());
                *s &= branch_condition.true_branch.clone();
                *t &= branch_condition.true_branch;
                let resource_moved_out = t.real_move_from_(
                    &resource_id,
                    &s[srcs[0]]
                        .content
                        .clone()
                        .map(|x| x.as_addr().unwrap().clone()),
                    datatypes,
                );
                s[dsts[0]].content =
                    resource_moved_out.map(|x| Value::Struct(x.as_datatype().unwrap()));
                Some(branch_condition.false_branch)
            }
            // Builtins
            // Destroy,
            ReadRef => {
                fn access_path_ty<'ctx, 'env, 'a, 'b>(
                    root_type: Type,
                    access_path: &[usize],
                    datatype: &'a Datatypes<'ctx, 'env>,
                ) -> Option<Type> {
                    if access_path.is_empty() {
                        Some(root_type)
                    } else {
                        match root_type {
                            Type::Struct(mod_id, struct_id, type_params) => {
                                let field_types = Type::instantiate_vec(
                                    datatype.get_field_types(mod_id, struct_id),
                                    &type_params,
                                );
                                access_path_ty(
                                    field_types[access_path[0]].clone(),
                                    &access_path[1..],
                                    datatype,
                                )
                            }
                            _ => None,
                        }
                    }
                }
                let refs = s[srcs[0]].content.clone();
                let ref_val = refs
                    .map(|x| match x {
                        Value::Reference(loc) => {
                            let root_ty = root_type(&s, loc.root.clone(), datatypes.clone());
                            let ref_ty = access_path_ty(
                                root_ty.clone(),
                                &loc.access_path,
                                &datatypes.borrow(),
                            );
                            read_ref(&s, t.clone(), loc.clone(), &root_ty, datatypes.clone())
                                .map(|x| Value::wrap(&x, &ref_ty.clone().unwrap()))
                        }
                        _ => unreachable!(),
                    })
                    .flatten();
                s[dsts[0]].content = ref_val;
                None
            }
            // WriteRef,
            WriteRef => {
                fn local_write_ref<'ctx, 'env>(
                    root_val: Dynamic<'ctx>,
                    root_ty: &Type,
                    access_path: &[FieldId],
                    hyper_field_val: Dynamic<'ctx>,
                    datatype: Rc<RefCell<Datatypes<'ctx, 'env>>>,
                ) -> Dynamic<'ctx> {
                    if !access_path.is_empty() {
                        match root_ty {
                            Type::Struct(mod_id, struct_id, type_params) => {
                                let field_types = Type::instantiate_vec(
                                    datatype.borrow().get_field_types(*mod_id, *struct_id),
                                    type_params,
                                );
                                let foo = datatype.borrow();
                                let (constructor, destructors) =
                                    foo.pack_unpack_(&root_ty).unwrap();
                                let fields: Vec<_> = destructors
                                    .iter()
                                    .enumerate()
                                    .map(|(field_num, destructor)| {
                                        if field_num == access_path[0] {
                                            local_write_ref(
                                                destructor.apply(&[&root_val]).simplify(),
                                                &field_types[field_num],
                                                &access_path[1..],
                                                hyper_field_val.clone(),
                                                datatype.clone(),
                                            )
                                        } else {
                                            destructor.apply(&[&root_val]).simplify()
                                        }
                                    })
                                    .collect();
                                let fields_ =
                                    &fields.iter().map(|x| x as &dyn Ast).collect::<Vec<_>>();
                                constructor.apply(fields_).simplify()
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        hyper_field_val
                    }
                }

                fn write_ref<'ctx, 'env>(
                    loc: Loc<'ctx>,
                    x: Value<'ctx>,
                    mut s: LocalState<'ctx>,
                    mut t: GlobalState<'ctx>,
                    datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
                ) -> (LocalState<'ctx>, GlobalState<'ctx>) {
                    let Loc { root, access_path } = loc;
                    match root.clone() {
                        Root::Local(local_index) => {
                            let root_vals =
                                read_ref_root(&s, t.clone(), root.clone(), datatypes.clone());
                            let root_ty = root_type(&s, root.clone(), datatypes.clone());
                            access_path_tys(
                                root_ty.clone(),
                                &access_path,
                                &mut datatypes.borrow_mut(),
                            );
                            let new_local_val = root_vals.map(|root_val| {
                                let dyn_val = local_write_ref(
                                    root_val.as_dynamic(),
                                    &root_ty,
                                    &access_path,
                                    x.clone().as_dynamic(),
                                    datatypes.clone(),
                                );
                                Value::wrap(&dyn_val, &root_ty)
                            });
                            s[local_index].content = new_local_val;
                            (s, t)
                        }
                        Root::Global(resource_id, addr) => {
                            let root_ty = root_type(&s, root.clone(), datatypes.clone());
                            access_path_tys(
                                root_ty.clone(),
                                &access_path,
                                &mut datatypes.borrow_mut(),
                            );
                            let updated_global_mem = t
                                .get_resource_value(&resource_id, datatypes.clone())
                                .map(|addr_resource| {
                                    let root_val = addr_resource.select(&addr);
                                    let raw_val = local_write_ref(
                                        root_val,
                                        &root_ty,
                                        &access_path,
                                        x.clone().as_dynamic(),
                                        datatypes.clone(),
                                    );
                                    addr_resource.store(&addr, &raw_val.as_datatype().unwrap())
                                });
                            t.resource_value.insert(resource_id, updated_global_mem);
                            (s, t)
                        }
                    }
                }

                let res = s[srcs[0]]
                    .content
                    .clone()
                    .prod(&s[srcs[1]].content)
                    .map(|(ref_, val)| {
                        if let Value::Reference(loc) = ref_ {
                            write_ref(loc, val, s.clone(), t.clone(), datatypes.clone())
                        } else {
                            unreachable!()
                        }
                    })
                    .0
                    .into_iter()
                    .map(
                        |Constrained {
                             content: (s, t),
                             constraint,
                         }| { (s & constraint.clone(), t & constraint) },
                    )
                    .fold(
                        (
                            LocalState {
                                context: s.get_ctx(),
                                ic: s.ic,
                                pc: s.pc.clone(),
                                ts: s.ts.clone(),
                                locals: s
                                    .locals
                                    .iter()
                                    .map(|x| Local {
                                        ty: x.ty.clone(),
                                        content: Disjoints(Vec::new()),
                                    })
                                    .collect(),
                            },
                            GlobalState {
                                ctx: t.ctx,
                                resource_value: BTreeMap::new(),
                                resource_existence: BTreeMap::new(),
                            },
                        ),
                        |(s, t), (s_, t_)| (s.merge(s_), t.merge(t_)),
                    );
                *s = res.0;
                *t = res.1;
                None
            }
            // FreezeRef,
            // Havoc(HavocKind),
            // Stop,
            // Memory model
            IsParent(_, _) => {
                let ctx = s.get_ctx();
                use z3::ast::Bool;
                s[dsts[0]].content = Disjoints(vec![Constrained::new(
                    Value::Primitive(PrimitiveValue::Bool(Bool::from_bool(ctx, false))),
                    s.pc.clone(),
                )]);
                None
            }
            // WriteBack(BorrowNode, BorrowEdge),
            WriteBack(_, _) => None,
            // UnpackRef,
            // PackRef,
            // UnpackRefDeep,
            // PackRefDeep,
            // Unary
            // CastU8 => todo!
            // CastU64 => todo!
            // CastU128 => todo!
            Not => pure_local_operation(
                dsts,
                |x: Vec<Value>| {
                    assert_eq!(x.len(), 1);
                    vec![!x.index(0)]
                },
                srcs,
                s,
            ),
            // Binary
            Add => pure_local_operation(
                dsts,
                |x: Vec<Value>| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) + x.index(1)]
                },
                srcs,
                s,
            ),
            Sub => pure_local_operation(
                dsts,
                |x: Vec<Value>| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) - x.index(1)]
                },
                srcs,
                s,
            ),
            Mul => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) * x.index(1)]
                },
                srcs,
                s,
            ),
            Div => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) / x.index(1)]
                },
                srcs,
                s,
            ),
            Mod => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) % x.index(1)]
                },
                srcs,
                s,
            ),
            BitOr => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) | x.index(1)]
                },
                srcs,
                s,
            ),
            BitAnd => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) & x.index(1)]
                },
                srcs,
                s,
            ),
            Xor => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) ^ x.index(1)]
                },
                srcs,
                s,
            ),
            // Shl,
            // Shr,
            Lt => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].lt(&x[1])]
                },
                srcs,
                s,
            ),
            Gt => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].gt(&x[1])]
                },
                srcs,
                s,
            ),
            Le => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].le(&x[1])]
                },
                srcs,
                s,
            ),
            Ge => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].ge(&x[1])]
                },
                srcs,
                s,
            ),
            Or => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].or(&x[1])]
                },
                srcs,
                s,
            ),
            And => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].and(&x[1])]
                },
                srcs,
                s,
            ),
            Eq => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].eq(&x[1])]
                },
                srcs,
                s,
            ),
            Neq => pure_local_operation(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].neq(&x[1])]
                },
                srcs,
                s,
            ),
            // CastU256,
            _ => None,
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::empty_locals;

        use super::*;
        use z3::{Context, Config};

        #[test]
        fn test_assign_move() {
            let cfg = Config::new();
            let ctx = Context::new(&cfg);
            let mut local_state = locals!(&ctx,
                U8(0), U8(42)
            );
            assign(0, 1, &AssignKind::Move, &mut local_state);
            assert!(local_state.len() == 2);
            assert!(local_state[1].is_empty());
            assert!(local_state[0] == Local::from_constant(&Constant::U8(42), &ctx));
        }

        #[test]
        fn test_assign_copy() {
            let cfg = Config::new();
            let ctx = Context::new(&cfg);
            let mut local_state = locals!(&ctx,
                U8(0), U8(42)
            );
            assign(0, 1, &AssignKind::Copy, &mut local_state);
            assert!(local_state[1] == Local::from_constant(&Constant::U8(42), &ctx));
            assert!(local_state[0] == Local::from_constant(&Constant::U8(42), &ctx));
        }

        #[test]
        fn test_assign_store() {
            let cfg = Config::new();
            let ctx = Context::new(&cfg);
            let mut local_state = locals!(&ctx,
                U8(0), U8(42)
            );
            assign(0, 1, &AssignKind::Copy, &mut local_state);
            assert!(local_state[1] == Local::from_constant(&Constant::U8(42), &ctx));
            assert!(local_state[0] == Local::from_constant(&Constant::U8(42), &ctx));
        }

        #[test]
        fn test_load() {
            let cfg = Config::new();
            let ctx = Context::new(&cfg);
            let mut local_state = empty_locals!(&ctx, Primitive(U8));
            assert!(local_state.len() == 1);
            assert!(local_state[0].is_empty());
            load(0, &Constant::U8(42), &mut local_state);
            assert!(local_state.len() == 1);
            assert!(local_state[0] == Local::from_constant(&Constant::U8(42), &ctx));
        }
    }
}

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
    fn accessors_along_path<'ctx, 'env, 'a>(
        mut root_type: Type,
        access_path: &[usize],
        datatype: &'a mut Datatypes<'ctx, 'env>,
    ) -> Option<Vec<&'a FuncDecl<'ctx>>> {
        access_path_tys(root_type.clone(), access_path, datatype);
        let mut res = Vec::new();
        for &edge in access_path {
            match root_type.clone() {
                Type::Struct(mod_id, struct_id, type_params) => {
                    let accessor = datatype.unpack(&root_type).unwrap().index(edge);
                    res.push(accessor);
                    let field_types = Type::instantiate_vec(
                        datatype.get_field_types(mod_id, struct_id),
                        &type_params,
                    );
                    root_type = field_types[edge].clone();
                }
                _ => return None,
            }
        }
        Some(res)
    }

    fn access_path_ty<'ctx, 'env, 'a, 'b>(
        root_type: Type,
        access_path: &[usize],
        datatype: &'a Datatypes<'ctx, 'env>,
    ) -> Option<Type> {
        if access_path.is_empty() {
            Some(root_type)
        } else {
            match root_type {
                Type::Struct(mod_id, struct_id, type_params) => {
                    let field_types = Type::instantiate_vec(
                        datatype.get_field_types(mod_id, struct_id),
                        &type_params,
                    );
                    access_path_ty(
                        field_types[access_path[0]].clone(),
                        &access_path[1..],
                        datatype,
                    )
                }
                _ => None,
            }
        }
    }

    fn access_path_tys<'ctx, 'env, 'a, 'b>(
        mut root_type: Type,
        access_path: &[usize],
        datatype: &'a mut Datatypes<'ctx, 'env>,
    ) {
        for &edge in access_path {
            match root_type {
                Type::Struct(module_id, struct_id, type_params) => {
                    datatype.insert(module_id, struct_id, type_params.clone());
                    let field_types = Type::instantiate_vec(
                        datatype.get_field_types(module_id, struct_id),
                        &type_params,
                    );
                    root_type = field_types[edge].clone();
                }
                _ => unreachable!(),
            }
        }
    }

    // accessors = f, g, ...
    // out: (... (g (f v)) ...)
    fn rep_select<'ctx>(v: Dynamic<'ctx>, accessors: &[&FuncDecl<'ctx>]) -> Dynamic<'ctx> {
        accessors
            .iter()
            .fold(v, |acc, accessor| accessor.apply(&[&acc]).simplify())
    }

    fn root_type<'ctx, 'env>(
        s: &LocalState<'ctx>,
        root: Root<'ctx>,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
    ) -> Type {
        match root {
            Root::Global(resource_id, _) => datatypes.borrow().get_resource_type(resource_id),
            Root::Local(local_index) => s[local_index].ty.clone(),
        }
    }

    fn read_ref_root<'env, 'ctx>(
        s: &LocalState<'ctx>,
        mut t: GlobalState<'ctx>,
        root: Root<'ctx>,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
    ) -> Disjoints<'ctx, Value<'ctx>> {
        match root {
            Root::Global(resource_id, addr) => {
                t.get_resource_value(&resource_id, datatypes)
                    .map(|addr_to_resource_val| {
                        Value::Struct(addr_to_resource_val.select(&addr).as_datatype().unwrap())
                    })
            }
            Root::Local(local_index) => s[local_index].content.clone(),
        }
    }

    fn read_ref<'env, 'ctx>(
        s: &LocalState<'ctx>,
        t: GlobalState<'ctx>,
        loc: Loc<'ctx>,
        root_type: &Type,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
    ) -> Disjoints<'ctx, Dynamic<'ctx>> {
        let Loc { root, access_path } = loc;
        let root_val = read_ref_root(s, t, root.clone(), datatypes.clone()).map(|x| x.as_dynamic());
        let datatypes_borrow = &mut datatypes.borrow_mut();
        let accessors =
            accessors_along_path(root_type.clone(), &access_path, datatypes_borrow).unwrap();
        root_val.map(|x| rep_select(x, &accessors[..]))
    }

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
            s[dsts[0]].content = Disjoints(vec![Constrained::new(
                Value::Reference(Loc {
                    root: Root::Local(srcs[0]),
                    access_path: Vec::new(),
                }),
                s.pc.clone(),
            )]);
            vec![(s, t)]
        }
        // BorrowField(ModuleId, StructId, Vec<Type>, usize),
        BorrowField(_, _, _, field_id) => {
            s[dsts[0]].content = s[srcs[0]].content.clone().map(|x| match x {
                Value::Reference(Loc { root, access_path }) => {
                    let mut new_access_path = access_path;
                    new_access_path.push(*field_id);
                    Value::Reference(Loc {
                        root,
                        access_path: new_access_path,
                    })
                }
                _ => unreachable!(),
            });
            vec![(s, t)]
        }
        // BorrowGlobal(ModuleId, StructId, Vec<Type>),
        BorrowGlobal(module_id, struct_id, type_params) => {
            s[dsts[0]].content = s[srcs[0]].content.clone().map(|x| {
                Value::Reference(Loc {
                    root: Root::Global(
                        new_resource_id(*module_id, *struct_id, type_params.clone()),
                        x.as_addr().unwrap().clone(),
                    ),
                    access_path: Vec::new(),
                })
            });
            vec![(s, t)]
        }
        // Get
        GetField(mod_id, struct_id, type_params, field_num) => {
            let mut datatypes_mut = datatypes.borrow_mut();
            let (_, accessors) = datatypes_mut
                .pack_unpack(&Type::Struct(*mod_id, *struct_id, type_params.clone()))
                .unwrap();
            let accessor = &accessors[*field_num];
            let dst_type = &s[dsts[0]].ty;
            s[dsts[0]].content = s[srcs[0]].content.clone().map(|x| {
                let unwrapped_res = accessor.apply(&[&x.as_dynamic()]).simplify();
                Value::wrap(&unwrapped_res, dst_type)
            });
            vec![(s, t)]
        }
        GetGlobal(mod_id, struct_id, type_params) => {
            let addr_val = s[srcs[0]].content.clone();
            let resource_id = new_resource_id(*mod_id, *struct_id, type_params.clone());
            let branch_condition = t
                .exists(&resource_id, &addr_val)
                .to_branch_condition(s.get_ctx());
            let mut true_branch_local_state = s.clone() & branch_condition.true_branch.clone();
            let mut true_branch_global_state = t.clone() & branch_condition.true_branch;
            let resource_moved_out = true_branch_global_state.real_move_from_(
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
        // Builtins
        // Destroy,
        ReadRef => {
            let refs = s[srcs[0]].content.clone();
            let ref_val = refs
                .map(|x| match x {
                    Value::Reference(loc) => {
                        let root_ty = root_type(&s, loc.root.clone(), datatypes.clone());
                        let ref_ty =
                            access_path_ty(root_ty.clone(), &loc.access_path, &datatypes.borrow());
                        read_ref(&s, t.clone(), loc.clone(), &root_ty, datatypes.clone())
                            .map(|x| Value::wrap(&x, &ref_ty.clone().unwrap()))
                    }
                    _ => unreachable!(),
                })
                .flatten();
            s[dsts[0]].content = ref_val;
            vec![(s, t)]
        }
        // WriteRef,
        WriteRef => {
            fn local_write_ref<'ctx, 'env>(
                root_val: Dynamic<'ctx>,
                root_ty: &Type,
                access_path: &[FieldId],
                hyper_field_val: Dynamic<'ctx>,
                datatype: Rc<RefCell<Datatypes<'ctx, 'env>>>,
            ) -> Dynamic<'ctx> {
                if !access_path.is_empty() {
                    match root_ty {
                        Type::Struct(mod_id, struct_id, type_params) => {
                            let field_types = Type::instantiate_vec(
                                datatype.borrow().get_field_types(*mod_id, *struct_id),
                                type_params,
                            );
                            let foo = datatype.borrow();
                            let (constructor, destructors) = foo.pack_unpack_(&root_ty).unwrap();
                            let fields: Vec<_> = destructors
                                .iter()
                                .enumerate()
                                .map(|(field_num, destructor)| {
                                    if field_num == access_path[0] {
                                        local_write_ref(
                                            destructor.apply(&[&root_val]).simplify(),
                                            &field_types[field_num],
                                            &access_path[1..],
                                            hyper_field_val.clone(),
                                            datatype.clone(),
                                        )
                                    } else {
                                        destructor.apply(&[&root_val]).simplify()
                                    }
                                })
                                .collect();
                            let fields_ = &fields.iter().map(|x| x as &dyn Ast).collect::<Vec<_>>();
                            constructor.apply(fields_).simplify()
                        }
                        _ => unreachable!(),
                    }
                } else {
                    hyper_field_val
                }
            }

            fn write_ref<'ctx, 'env>(
                loc: Loc<'ctx>,
                x: Value<'ctx>,
                mut s: LocalState<'ctx>,
                mut t: GlobalState<'ctx>,
                datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
            ) -> (LocalState<'ctx>, GlobalState<'ctx>) {
                let Loc { root, access_path } = loc;
                match root.clone() {
                    Root::Local(local_index) => {
                        let root_vals =
                            read_ref_root(&s, t.clone(), root.clone(), datatypes.clone());
                        let root_ty = root_type(&s, root.clone(), datatypes.clone());
                        access_path_tys(root_ty.clone(), &access_path, &mut datatypes.borrow_mut());
                        let new_local_val = root_vals.map(|root_val| {
                            let dyn_val = local_write_ref(
                                root_val.as_dynamic(),
                                &root_ty,
                                &access_path,
                                x.clone().as_dynamic(),
                                datatypes.clone(),
                            );
                            Value::wrap(&dyn_val, &root_ty)
                        });
                        s[local_index].content = new_local_val;
                        (s, t)
                    }
                    Root::Global(resource_id, addr) => {
                        let root_ty = root_type(&s, root.clone(), datatypes.clone());
                        access_path_tys(root_ty.clone(), &access_path, &mut datatypes.borrow_mut());
                        let updated_global_mem = t
                            .get_resource_value(&resource_id, datatypes.clone())
                            .map(|addr_resource| {
                                let root_val = addr_resource.select(&addr);
                                let raw_val = local_write_ref(
                                    root_val,
                                    &root_ty,
                                    &access_path,
                                    x.clone().as_dynamic(),
                                    datatypes.clone(),
                                );
                                addr_resource.store(&addr, &raw_val.as_datatype().unwrap())
                            });
                        t.resource_value.insert(resource_id, updated_global_mem);
                        (s, t)
                    }
                }
            }

            let res = s[srcs[0]]
                .content
                .clone()
                .prod(&s[srcs[1]].content)
                .map(|(ref_, val)| {
                    if let Value::Reference(loc) = ref_ {
                        write_ref(loc, val, s.clone(), t.clone(), datatypes.clone())
                    } else {
                        unreachable!()
                    }
                })
                .0
                .into_iter()
                .map(
                    |Constrained {
                         content: (s, t),
                         constraint,
                     }| { (s & constraint.clone(), t & constraint) },
                )
                .fold(
                    (
                        LocalState {
                            context: s.get_ctx(),
                            ic: s.ic,
                            pc: s.pc.clone(),
                            ts: s.ts.clone(),
                            locals: s
                                .locals
                                .iter()
                                .map(|x| Local {
                                    ty: x.ty.clone(),
                                    content: Disjoints(Vec::new()),
                                })
                                .collect(),
                        },
                        GlobalState {
                            ctx: t.ctx,
                            resource_value: BTreeMap::new(),
                            resource_existence: BTreeMap::new(),
                        },
                    ),
                    |(s, t), (s_, t_)| (s.merge(s_), t.merge(t_)),
                );
            vec![res]
        }
        // FreezeRef,
        // Havoc(HavocKind),
        // Stop,
        // Memory model
        IsParent(_, _) => {
            let ctx = s.get_ctx();
            use z3::ast::Bool;
            s[dsts[0]].content = Disjoints(vec![Constrained::new(
                Value::Primitive(PrimitiveValue::Bool(Bool::from_bool(ctx, false))),
                s.pc.clone(),
            )]);
            vec![(s, t)]
        }
        // WriteBack(BorrowNode, BorrowEdge),
        WriteBack(_, _) => vec![(s, t)],
        // UnpackRef,
        // PackRef,
        // UnpackRefDeep,
        // PackRefDeep,
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
