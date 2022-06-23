use crate::{dynamic::BranchCondition, traits::Applicative};

use super::*;

// # Local Variables ////////////////////////////////////////

/// Information about a local variable
#[derive(Clone)]
pub struct Local<'ctx> {
    /// Type of the local
    pub ty: Type,
    /// Values of the local
    pub(crate) content: Option<Values<'ctx>>,
}

impl<'ctx> Local<'ctx> {
    /// New local with type `ty` and no values.
    pub fn new(ty: Type) -> Self {
        Self {
            ty,
            content: None,
        }
    }

    /// Simplify each value.
    pub fn simplify(self) -> Self {
        Self {
            content: todo!(),
            ..self
        }
    }

    /// New local with name `x`, type `t`. Contains a new named symbolic value.
    pub fn from_type<'env, S: Into<Symbol>>(x: S, t: &Type, ctx: &'ctx Context, datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>) -> Self {
        Self {
            ty: t.clone(),
            content: Some(Values::pure(Value::new_const(x, t, ctx, datatypes))), // pure uses global ctx!!
        }
    }

    /// New local with a constant value.
    pub fn from_constant(c: &Constant, ctx: &'ctx Context) -> Self {
        Self {
            ty: type_of_constant(c),
            content: Some(Values::pure(Value::from_constant(c, ctx))), // pure uses global ctx!!
        }
    }

    /// Return the branch condition corresponding to the local (None if local is not a boolean).
    /// If the local is (x, p) ...,
    /// then the true branch is (or (and x p) ...),
    /// and the false branch is (or (and (not x) p) ...).
    pub fn to_branch_condition(&self, ctx: &'ctx Context) -> Option<BranchCondition<'ctx>> {
        todo!()
    }

    /// Set the content to empty, and return the original value.
    pub fn del(&mut self) -> Option<Values<'ctx>> {
        std::mem::replace(&mut self.content, None)
    }

    /// Return the number of possible values of the local.
    pub fn len(&self) -> usize {
        todo!()
    }

    /// Return the merge of the locals.
    pub fn merge(&mut self, other: Self, cond: OrderedConstraint<'ctx>) {
        todo!()
    }

    /// Return true iff the local has no value associated.
    /// For example, when a local is uninitiated or moved.
    pub fn is_empty(&self) -> bool {
        self.content.is_none()
    }
}

// trait implementations
impl<'ctx, 'env> fmt::Display for Local<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // write!(f, "{}", self.content.iter().format(", "))?;
        // Ok(())
        todo!()
    }
}

// # Local Memory ////////////////////////////////////////

/// Local Memory
/// 
/// A fixed length vector of local variables
#[derive(Clone)]
pub struct LocalMemory<'ctx> {
    pub(crate) context: &'ctx Context,
    pub locals: Vec<Local<'ctx>>,
}

impl<'ctx> LocalMemory<'ctx> {
    pub fn new(
        context: &'ctx Context,
        locals: Vec<Local<'ctx>>,
    ) -> Self {
        Self {
            context,
            locals,
        }
    }

    /// Merge the locals in `mask`.
    pub fn merge(&mut self, other: Self, cond: OrderedConstraint<'ctx>, mask: impl Iterator<Item=TempIndex>) {
        for local_index in mask {
            self[local_index].merge(other[local_index].clone(), cond.clone()) // todo! this is unnecessarily inefficient
        }
    }

    /// Return constrained tuples of operation arguments.
    /// If an operation has args ... t_i ...
    /// where t_i = ... (x_i_j, p_i_j) ...
    /// then the return value should be equivalent to
    /// ... ((... x_i_j ...), (and ... p_i_j ...)) ...
    pub fn args(&self, srcs: &[TempIndex]) -> SymbolicTree<OrderedConstraint<'ctx>, Vec<Value<'ctx>>> {
        todo!()
    }

    pub fn get_ctx(&self) -> &'ctx Context {
        &self.context
    }

    /// Set `var` to empty and return the original values of `var`.
    pub fn del(&mut self, var: TempIndex) -> Option<Values<'ctx>> {
        self.index_mut(var).del()
    }

    /// Number of locals.
    pub fn len(&self) -> usize {
        self.locals.len()
    }
}

// traits for LocalMem
use std::{ops::{Index, IndexMut}, mem::take};

impl<'ctx> Index<TempIndex> for LocalMemory<'ctx> {
    type Output = Local<'ctx>;

    /// Return the local variable at `index`
    fn index(&self, index: TempIndex) -> &Self::Output {
        self.locals.index(index)
    }
}

impl<'ctx> IndexMut<TempIndex> for LocalMemory<'ctx> {
    fn index_mut(&mut self, index: TempIndex) -> &mut Self::Output {
        self.locals.index_mut(index)
    }
}

impl<'ctx, 'env> fmt::Display for LocalMemory<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Locals:")?;
        for (i, local) in self.locals.iter().enumerate() {
            writeln!(f, "$t{} = {}", i, local)?;
        }
        Ok(())
    }
}