use std::{
    cell::RefCell,
    collections::BTreeMap,
    ops::{Index, IndexMut, BitOr},
    rc::Rc,
};

use move_model::model::QualifiedInstId;
use move_stackless_bytecode::stackless_bytecode::{
    AbortAction, AssignKind, Constant, Operation,
};
use z3::{
    ast::{Ast, Dynamic, Bool}, FuncDecl, Context,
};

use crate::{
    constraint::{Constrained, Constraint, OrderedConstraint},
    symbolic_tree::{SymbolicTree},
    ty::{new_resource_id, Datatypes, FieldId, Type},
    value::{ConstrainedValue, Loc, PrimitiveValue, Root, Value}, state::{TempIndex, LocalMemory, GlobalMemory, EvalState, Local, Values},
    traits::{Applicative, Functor, Monoidal},
};

// Evaluate an `Assign`.
fn assign<'ctx>(dst: TempIndex, src: TempIndex, kind: &AssignKind, loc_mem: &mut LocalMemory<'ctx>) {
    let src_val = match kind {
        AssignKind::Move => loc_mem.del(src),
        AssignKind::Copy | AssignKind::Store => loc_mem.index(src).content.clone(),
    };
    loc_mem[dst].content = src_val;
}

// Evaluate a `Load`.
fn load<'ctx>(dst: TempIndex, c: &Constant, loc_mem: &mut LocalMemory<'ctx>) {
    loc_mem[dst].content = Some(Values::pure(Value::from_constant(c, loc_mem.context)));
}

// Handle pure operations.
// the arity of inputs is checked in `op`
fn pure_local_operation<'ctx, F>(
    dsts: &[TempIndex],
    op: F,
    srcs: &[TempIndex],
    loc_mem: &mut LocalMemory<'ctx>,
) where
    F: Fn(Vec<Value<'ctx>>) -> Vec<Value<'ctx>> + Clone,
{
    let constrained_args = loc_mem.args(srcs);
    let dests_val = constrained_args.map(op);
    for &x in dsts {
        loc_mem.index_mut(x).del();
    }
    for (i, &x) in dsts.iter().enumerate() {
        loc_mem[x].content = Some(dests_val.clone().map(|vals| {
            debug_assert!(vals.len() == dsts.len());
            vals[i].clone() // todo! unnecessary clone
        }));
    }
}

// executes operation on `loc_mem`, `glob_mem` and return abort condition
fn operation<'ctx, 'env>(
    dsts: &[TempIndex],
    op: &Operation,
    srcs: &[TempIndex],
    _on_abort: Option<&AbortAction>,
    eval_state: &mut EvalState<'ctx>,
    datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
) -> Option<Constraint<'ctx>> {
    let loc_mem = &mut eval_state.local_memory;
    let glob_mem = &mut eval_state.global_memory;
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
    fn root_type<'ctx, 'env>(loc_mem: &LocalMemory<'ctx>, root: Root<'ctx>) -> Type {
        match root {
            Root::Global(resource_id, _) => {
                Type::Struct(resource_id.module_id, resource_id.id, resource_id.inst)
            }
            Root::Local(local_index) => loc_mem[local_index].ty.clone(),
        }
    }

    // Return value at `root`
    fn read_ref_root<'env, 'ctx>(
        loc_mem: &LocalMemory<'ctx>,
        mut glob_mem: GlobalMemory<'ctx>,
        root: Root<'ctx>,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
    ) -> Values<'ctx> {
        match root {
            Root::Global(resource_id, addr) => {
                glob_mem.get_resource_value(&resource_id, datatypes)
                    .map(|addr_to_resource_val| {
                        Value::Struct(addr_to_resource_val.select(&addr).as_datatype().unwrap())
                    })
            }
            Root::Local(local_index) => loc_mem[local_index].content.clone().unwrap(),
        }
    }

    // Return value at `loc`
    fn read_ref<'env, 'ctx>(
        loc_mem: &LocalMemory<'ctx>,
        glob_mem: GlobalMemory<'ctx>,
        loc: Loc<'ctx>,
        root_type: &Type,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
    ) -> SymbolicTree<OrderedConstraint<'ctx>, Dynamic<'ctx>> {
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
        let root_val = read_ref_root(loc_mem, glob_mem, root.clone(), datatypes.clone()).map(|x| x.as_dynamic());
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
        loc_mem: &mut LocalMemory<'ctx>,
    ) -> Option<Constraint<'ctx>>
    where
        F: Fn(Vec<Value<'ctx>>) -> Vec<Value<'ctx>> + Clone,
    {
        crate::dynamic::pure_local_operation(dsts, op, srcs, loc_mem);
        None
    }

    use Operation::*;
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
            loc_mem,
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
                    .map(|(f, glob_mem)| Value::wrap(&f.apply(&[x[0].unwrap()]).simplify(), &glob_mem))
                    .collect()
            },
            srcs,
            loc_mem,
        ),

        // Resources
        MoveTo(module_id, struct_id, type_params) => {
            let addr_val = loc_mem[srcs[0]].content.clone();
            let resource_type = QualifiedInstId {
                module_id: *module_id,
                inst: type_params.clone(),
                id: *struct_id,
            };
            let branch_condition = BranchCondition::from(
                glob_mem
                .exists(&resource_type, addr_val.unwrap())
            );
            glob_mem.real_move_to(
                &resource_type,
                loc_mem[srcs[0]]
                    .content
                    .as_ref()
                    .expect(format!("{} is uninitialized or moved", srcs[0]).as_str())
                    .clone()
                    .map(|x| x.as_addr().unwrap().clone()),
                loc_mem[srcs[1]]
                    .content
                    .as_ref()
                    .expect(format!("{} is uninitialized or moved", srcs[1]).as_str())
                    .clone()
                    .map(|x| x.as_datatype().unwrap().clone()),
                datatypes,
            );
            Some(branch_condition.true_branch)
        }
        MoveFrom(module_id, struct_id, type_params) => {
            let addr_val = loc_mem[srcs[0]].content.clone();
            let resource_id = new_resource_id(*module_id, *struct_id, type_params.clone());
            let branch_condition = BranchCondition::from(
                glob_mem
                .exists(&resource_id, addr_val.unwrap())
            );
            let resource_moved_out = glob_mem.real_move_from(
                &resource_id,
                loc_mem[srcs[0]]
                    .content
                    .as_ref()
                    .expect(format!("{} is uninitialized or moved", srcs[0]).as_str())
                    .clone()
                    .map(|x| x.as_addr().unwrap().clone()),
                datatypes,
            );
            loc_mem[dsts[0]].content =
                Some(resource_moved_out.map(|x| Value::Struct(x.as_datatype().unwrap())));
            Some(branch_condition.false_branch)
        }
        Exists(module_id, struct_id, type_params) => {
            let dst = dsts[0];
            let src = srcs[0];
            let src_val =
                loc_mem[src]
                .content
                .as_ref()
                .expect(format!("{} is uninitialized or moved", srcs[0]).as_str())
                .clone();
            let resource_type = QualifiedInstId {
                module_id: *module_id,
                inst: type_params.clone(),
                id: *struct_id,
            };
            loc_mem[dst].content = Some(
                glob_mem
                .exists(&resource_type, src_val)
                .map(|x| Value::Primitive(PrimitiveValue::Bool(x)))
            );
            None
        }

        // Borrow
        // BorrowLoc,
        BorrowLoc => {
            loc_mem[dsts[0]].content = Some(
                Values::pure(
                    Value::Reference(Loc {
                        root: Root::Local(srcs[0]),
                        access_path: Vec::new(),
                    })
                )
            );
            None
        }
        // BorrowField(ModuleId, StructId, Vec<Type>, usize),
        BorrowField(_, _, _, field_id) => {
            loc_mem[dsts[0]].content = Some(
                loc_mem[srcs[0]]
                .content
                .as_ref()
                .expect(format!("{} is uninitialized or moved", srcs[0]).as_str())
                .clone()
                .map(|x| match x {
                    Value::Reference(Loc { root, access_path }) => {
                        let mut new_access_path = access_path;
                        new_access_path.push(*field_id);
                        Value::Reference(Loc {
                            root,
                            access_path: new_access_path,
                        })
                    }
                    _ => unreachable!(),
                })
            );
            None
        }
        // BorrowGlobal(ModuleId, StructId, Vec<Type>),
        BorrowGlobal(module_id, struct_id, type_params) => {
            loc_mem[dsts[0]].content = Some(
                loc_mem[srcs[0]]
                .content
                .as_ref()
                .expect(format!("{} is uninitialized or moved", srcs[0]).as_str())
                .clone()
                .map(|x| {
                    Value::Reference(Loc {
                        root: Root::Global(
                            new_resource_id(*module_id, *struct_id, type_params.clone()),
                            x.as_addr().unwrap().clone(),
                        ),
                        access_path: Vec::new(),
                   })
                })
            );
            None
        }
        // Get
        GetField(mod_id, struct_id, type_params, field_num) => {
            let mut datatypes_mut = datatypes.borrow_mut();
            let (_, accessors) = datatypes_mut
                .pack_unpack(&Type::Struct(*mod_id, *struct_id, type_params.clone()))
                .unwrap();
            let accessor = &accessors[*field_num];
            let dst_type = &loc_mem[dsts[0]].ty;
            loc_mem[dsts[0]].content = Some(
                loc_mem[srcs[0]]
                .content
                .as_ref()
                .expect(format!("{} is uninitialized or moved", srcs[0]).as_str())
                .clone()
                .map(|x| {
                    let unwrapped_res = accessor.apply(&[&x.as_dynamic()]).simplify();
                    Value::wrap(&unwrapped_res, dst_type)
                })
            );
            None
        }
        GetGlobal(mod_id, struct_id, type_params) => {
            let addr_val = loc_mem[srcs[0]].content.clone();
            let resource_id = new_resource_id(*mod_id, *struct_id, type_params.clone());
            let branch_condition = 
                BranchCondition::from(
                    glob_mem
                    .exists(
                        &resource_id, 
                        addr_val.expect("accessing uninitialized or moved local")
                    )
                );
            let resource_moved_out = glob_mem.real_move_from_(
                &resource_id,
                loc_mem[srcs[0]]
                    .content
                    .as_ref()
                    .expect(format!("{} is uninitialized or moved", srcs[0]).as_str())
                    .clone()
                    .map(|x| x.as_addr().unwrap().clone()),
                datatypes,
            );
            loc_mem[dsts[0]].content = Some(
                resource_moved_out.map(|x| Value::Struct(x.as_datatype().unwrap()))
            );
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
            let refs = loc_mem[srcs[0]].content.clone();
            let ref_val = todo!();
            // refs
            //     .map(|x| match x {
            //         Value::Reference(loc) => {
            //             let root_ty = root_type(&loc_mem, loc.root.clone());
            //             let ref_ty =
            //                 access_path_ty(root_ty.clone(), &loc.access_path, &datatypes.borrow());
            //             read_ref(&loc_mem, glob_mem.clone(), loc.clone(), &root_ty, datatypes.clone())
            //                 .map(|x| Value::wrap(&x, &ref_ty.clone().unwrap()))
            //         }
            //         _ => unreachable!(),
            //     })
            //     .flatten();
            loc_mem[dsts[0]].content = ref_val;
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
                mut loc_mem: LocalMemory<'ctx>,
                mut glob_mem: GlobalMemory<'ctx>,
                datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>,
            ) -> (LocalMemory<'ctx>, GlobalMemory<'ctx>) {
                let Loc { root, access_path } = loc;
                match root.clone() {
                    Root::Local(local_index) => {
                        let root_vals =
                            read_ref_root(&loc_mem, glob_mem.clone(), root.clone(), datatypes.clone());
                        let root_ty = root_type(&loc_mem, root.clone());
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
                        loc_mem[local_index].content = Some(new_local_val);
                        (loc_mem, glob_mem)
                    }
                    Root::Global(resource_id, addr) => {
                        let root_ty = root_type(&loc_mem, root.clone());
                        access_path_tys(root_ty.clone(), &access_path, &mut datatypes.borrow_mut());
                        let updated_global_mem = glob_mem
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
                        glob_mem.resource_value.insert(resource_id, updated_global_mem);
                        (loc_mem, glob_mem)
                    }
                }
            }
            todo!();
            // let res = loc_mem[srcs[0]]
            //     .content
            //     .expect(format!("{} uninitialized or moved", srcs[0]).as_str())
            //     .clone()
            //     .prod(
            //         loc_mem[srcs[1]]
            //         .content
            //         .expect(format!("{} uninitialized or moved", srcs[1]).as_str())
            //         .clone()
            //     )
            //     .map(|(ref_, val)| {
            //         if let Value::Reference(loc) = ref_ {
            //             write_ref(loc, val, loc_mem.clone(), glob_mem.clone(), datatypes.clone())
            //         } else {
            //             unreachable!()
            //         }
            //     })
            //     .0
            //     .into_iter()
            //     .map(
            //         |Constrained {
            //              content: (loc_mem, glob_mem),
            //              constraint,
            //          }| { (loc_mem & constraint.clone(), glob_mem & constraint) },
            //     )
            //     .fold(
            //         (
            //             LocalMemory {
            //                 context: loc_mem.get_ctx(),
            //                 locals: loc_mem
            //                     .locals
            //                     .iter()
            //                     .map(|x| Local {
            //                         ty: x.ty.clone(),
            //                         content: Disjoints(Vec::new()),
            //                     })
            //                     .collect(),
            //             },
            //             GlobalMemory {
            //                 ctx: glob_mem.ctx,
            //                 resource_value: BTreeMap::new(),
            //                 resource_existence: BTreeMap::new(),
            //             },
            //         ),
            //         |(loc_mem, glob_mem), (s_, t_)| (loc_mem.merge(s_), glob_mem.merge(t_)),
            //     );
            // *loc_mem = res.0;
            // *glob_mem = res.1;
            None
        }
        // FreezeRef,
        // Havoc(HavocKind),
        // Stop,
        // Memory model
        // IsParent(_, _) => {
        //     let ctx = loc_mem.get_ctx();
        //     use z3::ast::Bool;
        //     loc_mem[dsts[0]].content = Disjoints(vec![Constrained::new(
        //         Value::Primitive(PrimitiveValue::Bool(Bool::from_bool(ctx, false))),
        //         loc_mem.pc.clone(),
        //     )]);
        //     None
        // }
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
            loc_mem,
        ),
        // Binary
        Add => pure_local_operation(
            dsts,
            |x: Vec<Value>| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) + x.index(1)]
            },
            srcs,
            loc_mem,
        ),
        Sub => pure_local_operation(
            dsts,
            |x: Vec<Value>| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) - x.index(1)]
            },
            srcs,
            loc_mem,
        ),
        Mul => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) * x.index(1)]
            },
            srcs,
            loc_mem,
        ),
        Div => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) / x.index(1)]
            },
            srcs,
            loc_mem,
        ),
        Mod => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) % x.index(1)]
            },
            srcs,
            loc_mem,
        ),
        BitOr => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) | x.index(1)]
            },
            srcs,
            loc_mem,
        ),
        BitAnd => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) & x.index(1)]
            },
            srcs,
            loc_mem,
        ),
        Xor => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x.index(0) ^ x.index(1)]
            },
            srcs,
            loc_mem,
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
            loc_mem,
        ),
        Gt => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].gt(&x[1])]
            },
            srcs,
            loc_mem,
        ),
        Le => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].le(&x[1])]
            },
            srcs,
            loc_mem,
        ),
        Ge => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].ge(&x[1])]
            },
            srcs,
            loc_mem,
        ),
        Or => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].or(&x[1])]
            },
            srcs,
            loc_mem,
        ),
        And => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].and(&x[1])]
            },
            srcs,
            loc_mem,
        ),
        Eq => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].eq(&x[1])]
            },
            srcs,
            loc_mem,
        ),
        Neq => pure_local_operation(
            dsts,
            |x| {
                assert_eq!(x.len(), 2);
                vec![x[0].neq(&x[1])]
            },
            srcs,
            loc_mem,
        ),
        // CastU256,
        _ => None,
    }
}

/// A pair of disjoint constraints. So true_branch & false_branch is never satisfiable.
pub struct BranchCondition<'ctx> {
    pub true_branch: Constraint<'ctx>,
    pub false_branch: Constraint<'ctx>,
}
  
impl<'ctx> BitOr for BranchCondition<'ctx> {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
        (
            BranchCondition { true_branch: t1, false_branch: f1 },
            BranchCondition { true_branch: t2, false_branch: f2 },
        ) => BranchCondition { true_branch: t1 | t2, false_branch: f1 | f2 },
        }
    }
}

impl<'ctx> BranchCondition<'ctx> {
    /// The identity element of the | operation.
    pub fn or_id(ctx: &'ctx Context) -> Self {
        BranchCondition { true_branch: Bool::from_bool(ctx, false), false_branch: Bool::from_bool(ctx, false) }
    }

    /// Simplify fields.
    pub fn simplify(self) -> Self {
        match self {
        BranchCondition { true_branch, false_branch } => BranchCondition { true_branch: true_branch.simplify(), false_branch: false_branch.simplify() }
        }
    }
}

impl<'ctx> From<SymbolicTree<OrderedConstraint<'ctx>, Constraint<'ctx>>> for BranchCondition<'ctx> {
    fn from(t: SymbolicTree<OrderedConstraint<'ctx>, Constraint<'ctx>>) -> Self {
        match t {
            SymbolicTree::Node(v) => BranchCondition { true_branch: v.clone(), false_branch: !v.clone()},
            SymbolicTree::Leaf(l, p, r) => {
                let left_recur = BranchCondition::from(*l);
                let right_recur = BranchCondition::from(*r);
                BranchCondition {
                    true_branch: left_recur.true_branch & &p.constraint| right_recur.true_branch & !&p.constraint,
                    false_branch: left_recur.false_branch & &p.constraint | right_recur.false_branch & !p.constraint,
                }
            }
        }
    }
}


#[cfg(test)]
mod tests {
}