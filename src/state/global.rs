use super::*;
/// Global Memory
/// 
/// Family of partial maps from account address to resouce value, indexed by resource type.
/// The partial map consists of a map from adress to bool, indicating if the resouce exists,
/// and another map from adress to the resource value hold.
#[derive(Clone)]
pub struct GlobalMemory<'ctx> {
    pub(crate) ctx: &'ctx Context,
    /// Map from account address to resource hold
    pub resource_value: BTreeMap<ResourceId, Disjoints<'ctx, Array<'ctx>>>,
    /// Map from account address to bool, where false indicates the account doesn't hold the resource
    pub resource_existence: BTreeMap<ResourceId, Disjoints<'ctx, Array<'ctx>>>,
}

impl<'ctx> GlobalMemory<'ctx> {
    /// Create an empty global memory.
    pub fn new_empty(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            resource_value: BTreeMap::new(),
            resource_existence: BTreeMap::new(),
        }
    }

    pub fn merge(self, other: Self) -> Self {
        fn merge<'ctx>(x: BTreeMap<ResourceId, Disjoints<'ctx, Array<'ctx>>>, y: BTreeMap<ResourceId, Disjoints<'ctx, Array<'ctx>>>) -> BTreeMap<ResourceId, Disjoints<'ctx, Array<'ctx>>> {
            let mut res = x;
            for (resource_id, mut disjoints) in y {
                res.entry(resource_id)
                    .and_modify(|x| x.0.append(&mut disjoints.0))
                    .or_insert(disjoints);
            }
            res
        }
        assert!(self.ctx == other.ctx);
        GlobalMemory { 
            ctx: self.ctx,
            resource_value: merge(self.resource_value, other.resource_value),
            resource_existence: merge(self.resource_existence, other.resource_existence)
        }
    }

    pub fn get_ctx(&self) -> &'ctx Context {
        self.ctx
    }

    // Initialize resource value.
    // acquire: called only when `resource` is not in `resource_value`.
    fn init_resource_value<'env>(&mut self, datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>, resource: &ResourceId) {
        let init_val: ConstrainedArray<'ctx> = Constrained {
            content: Array::fresh_const(
                self.get_ctx(),
                "global memory",
                &Sort::bitvector(self.get_ctx(), PrimitiveValue::ADDR_LENGTH),
                &datatypes.borrow_mut().from_struct(&resource).sort,
            ),
            constraint: Bool::from_bool(self.get_ctx(), true),
        };
        self.resource_value
            .insert(resource.clone(), Disjoints(vec![init_val]));
    }

    // Similar to `init_resource_value`.
    fn init_resource_existence(&mut self, resource: &ResourceId) {
        let init_val: ConstrainedArray<'ctx> = Constrained {
            content: Array::fresh_const(
                self.get_ctx(),
                "global memory domain",
                &Sort::bitvector(self.get_ctx(), PrimitiveValue::ADDR_LENGTH),
                &Sort::bool(self.get_ctx()),
            ),
            constraint: Bool::from_bool(self.get_ctx(), true),
        };
        self.resource_existence
            .insert(resource.clone(), Disjoints(vec![init_val]));
    }

    /// Get the resource existence map indexed by `resouce`.
    /// If the map doesn't exist, create a fresh one.
    pub fn get_resource_existence(
        &mut self,
        resource: &ResourceId,
    ) -> Disjoints<'ctx, Array<'ctx>> {
        match self.resource_existence.get(resource) {
            Some(arrays) => arrays.clone(),
            None => {
                self.init_resource_existence(resource);
                self.get_resource_existence(resource).clone()
            }
        }
    }

    /// Get the resource existence map indexed by `resouce`.
    /// If the map doesn't exist, create a fresh one.
    pub fn get_resource_value<'env>(
        &mut self,
        resource: &ResourceId,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
    ) -> Disjoints<'ctx, Array<'ctx>> {
        match self.resource_value.get(resource) {
            Some(arrays) => arrays.clone(),
            None => {
                self.init_resource_value(datatypes.clone(), resource);
                self.get_resource_value(resource, datatypes)
            }
        }
    }

    /// Return the condition that `resource_type` exists.
    /// A fresh resource_existence map at `resource_typ` is created if it doesn't exist.
    pub fn exists(
        &mut self,
        resource_type: &ResourceId,
        addr: &Disjoints<'ctx, Value<'ctx>>,
    ) -> Disjoints<'ctx, Constraint<'ctx>> {
        let resource_existence = self.get_resource_existence(resource_type);
        resource_existence
            .prod(addr)
            .map(|(array, value)| {
                array
                    .select(value.as_addr().unwrap())
                    .as_bool()
                    .expect("resource_existence contains non-boolean")
        })
    }

    pub fn real_move_to<'env>(
        &mut self,
        resource_type: &ResourceId,
        addrs: &Disjoints<'ctx, BV<'ctx>>,
        resource: Disjoints<'ctx, Datatype<'ctx>>,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
    ) {
        // update resource value map so that addr contains value
        // update resource existence map so that addr contains true
        match self.resource_value.get(resource_type) {
            Some(resource_value_maps) => {
                let resource_vals: Disjoints<'ctx, Datatype<'ctx>> = resource;
                let new_resource_value_map = resource_value_maps
                    .prod(addrs)
                    .prod(&resource_vals)
                    .map(|((array, addr), resource_val)| array.store(&addr, &resource_val));
                let resource_existence_map: &Disjoints<Array> =
                    self.resource_existence.get(resource_type).unwrap(); // already inited when checking for existence
                let new_resource_existence_map =
                    resource_existence_map
                        .prod(addrs)
                        .map(|(array, addr)| {
                            array.store(&addr, &Bool::from_bool(self.get_ctx(), true))
                        });
                self.resource_value
                    .insert(resource_type.clone(), new_resource_value_map);
                self.resource_existence
                    .insert(resource_type.clone(), new_resource_existence_map);
            }
            None => {
                self.init_resource_value(datatypes.clone(), resource_type);
                self.real_move_to(resource_type, addrs, resource, datatypes);
            }
        }
    }

    pub fn real_move_from<'env>(
        &mut self,
        resource_type: &ResourceId,
        addrs: &Disjoints<'ctx, BV<'ctx>>,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
    ) -> Disjoints<'ctx, Dynamic<'ctx>> {
        // update resource value map so that addr contains value
        // update resource existence map so that addr contains true
        match self.resource_value.get(resource_type) {
            Some(resource_value_maps) => {
                let ret_vals = resource_value_maps.prod(addrs).map(
                    |(global_mem, addr)| global_mem.select(&addr)
                );
                let resource_existence_map: &Disjoints<Array> =
                    self.resource_existence.get(resource_type).unwrap(); // already inited when checking for existence
                let new_resource_existence_map = resource_existence_map
                    .prod(addrs)
                    .map(|(array, addr)| array.store(&addr, &Bool::from_bool(self.get_ctx(), false)));
                self.resource_existence
                    .insert(resource_type.clone(), new_resource_existence_map);
                ret_vals
            }
            None => {
                self.init_resource_value(datatypes.clone(), resource_type);
                self.real_move_from(resource_type, addrs, datatypes)
            }
        }
    }

    pub fn real_move_from_<'env>(
        &mut self,
        resource_type: &ResourceId,
        addrs: &Disjoints<'ctx, BV<'ctx>>,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
    ) -> Disjoints<'ctx, Dynamic<'ctx>> {
        // update resource value map so that addr contains value
        // update resource existence map so that addr contains true
        match self.resource_value.get(resource_type) {
            Some(resource_value_maps) => {
                let ret_vals = resource_value_maps.prod(addrs).map(
                    |(global_mem, addr)| global_mem.select(&addr)
                );
                ret_vals
            }
            None => {
                self.init_resource_value(datatypes.clone(), resource_type);
                self.real_move_from(resource_type, addrs, datatypes)
            }
        }
    }
}

/// Add constraint
impl<'ctx> BitAnd<Bool<'ctx>> for GlobalMemory<'ctx> {
    type Output = Self;

    fn bitand(self, rhs: Bool<'ctx>) -> Self::Output {
        match self {
            GlobalMemory { ctx, resource_value, resource_existence } => {
                GlobalMemory {
                    ctx,
                    resource_value: resource_value.into_iter().map(|(k, v)| (k, v & &rhs)).collect(),
                    resource_existence: resource_existence.into_iter().map(|(k, v)| (k, v & &rhs)).collect(),
                }
            }
        }
    }
}

impl<'ctx> BitAndAssign<Constraint<'ctx>> for GlobalMemory<'ctx> {
    fn bitand_assign(&mut self, rhs: Constraint<'ctx>) {
        for (_, v) in self.resource_value.iter_mut() {
            *v &= &rhs;
        }
        for (_, v) in self.resource_existence.iter_mut() {
            *v &= &rhs;
        }
    }
}

pub type ConstrainedArray<'ctx> = Constrained<'ctx, Array<'ctx>>;