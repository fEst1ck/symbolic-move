use crate::dynamic::BranchCondition;

use super::*;

// # Local Variables ////////////////////////////////////////

/// Information about a local variable
#[derive(Clone, PartialEq)]
pub struct Local<'ctx> {
    /// Type of the local
    pub ty: Type,
    /// Values of the local
    pub(crate) content: Disjoints<'ctx, Value<'ctx>>,
}

impl<'ctx> Local<'ctx> {
    /// New local with type `ty` and no values.
    pub fn new(ty: Type) -> Self {
        Self {
            ty,
            content: Disjoints(Vec::new()),
        }
    }

    /// Simplify each value.
    pub fn simplify(self) -> Self {
        Self {
            content: self.content.into_iter().map(|x| x.simplify()).collect(),
            ..self
        }
    }

    /// New local with name `x`, type `t`. Contains a fresh symbolic value.
    pub fn from_type<'env, S: Into<Symbol>>(x: S, t: &Type, ctx: &'ctx Context, datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>) -> Self {
        Self {
            ty: t.clone(),
            content: Disjoints(vec![ConstrainedValue::new_const(x, t, ctx, datatypes)]),
        }
    }

    /// New local with a constant value.
    pub fn from_constant(c: &Constant, ctx: &'ctx Context) -> Self {
        Self { ty: type_of_constant(c), content: Disjoints::from_constrained(Constrained::pure(Value::from_constant(c, ctx), ctx)) }
    }

    /// Return the branch condition corresponding to the local (None if local is not a boolean).
    /// If the local is (x, p) ...,
    /// then the true branch is (or (and x p) ...),
    /// and the false branch is (or (and (not x) p) ...).
    pub fn to_branch_condition(&self, ctx: &'ctx Context) -> Option<BranchCondition<'ctx>> {
        let mut acc = BranchCondition::or_id(ctx);
        for cv in self.content.clone() {
            match cv.to_branch_condition() {
                Some(bc) => acc = (acc | bc).simplify(),
                None => return None
            }
        }
        Some(acc)
    }

    /// Set the content to empty, and return the original value.
    pub fn del(&mut self) -> Disjoints<'ctx, Value<'ctx>> {
        std::mem::replace(&mut self.content, Disjoints(Vec::new()))
    }

    /// Return the number of possible values of the local.
    pub fn len(&self) -> usize {
        self.content.0.len()
    }

    /// Return the merge of the locals.
    pub fn merge(mut self, mut other: Self) -> Self {
        fn merge_content<'ctx>(
            xs: Vec<ConstrainedValue<'ctx>>,
            ys: Vec<ConstrainedValue<'ctx>>,
        ) -> Vec<ConstrainedValue<'ctx>> {
            let mut res = Vec::with_capacity(xs.len());
            for (x, y) in xs.into_iter().zip(ys.into_iter()) {
                res.append(&mut x.merge(y));
            }
            res
        }
        if self.len() == other.len() {
            Self {
                ty: {
                    assert!(self.ty == other.ty);
                    self.ty
                },
                content: Disjoints(merge_content(self.content.0, other.content.0)),
            }
        } else {
            self.content.0.append(&mut other.content.0);
            self
        }
    }

    /// Return true iff the local has no value associated.
    /// For example, when a local is uninitiated or moved.
    pub fn is_empty(&self) -> bool {
        self.content.0.is_empty()
    }
}

// trait implementations
impl<'ctx, 'env> fmt::Display for Local<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.content.iter().format(", "))?;
        Ok(())
    }
}

/// Add constraint to a local.
impl<'ctx> BitAnd<Bool<'ctx>> for Local<'ctx> {
    type Output = Self;

    /// (x, p) ... & q -> (x, p & q) ...
    fn bitand(self, rhs: Bool<'ctx>) -> Self::Output {
        Local { content: self.content & rhs, ..self }
    }
}

impl<'ctx> BitAndAssign<Bool<'ctx>> for Local<'ctx> {
    fn bitand_assign(&mut self, rhs: Bool<'ctx>) {
        self.content &= rhs;
    }
}

impl<'ctx> BitAndAssign<&Bool<'ctx>> for Local<'ctx> {
    fn bitand_assign(&mut self, rhs: &Bool<'ctx>) {
        self.content &= rhs;
    }
}

/// Merge locals
impl<'ctx> BitOr<Local<'ctx>> for Local<'ctx> {
    type Output = Self;

    fn bitor(self, rhs: Local<'ctx>) -> Self {
        self.merge(rhs)
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

    pub fn merge(self, other: Self) -> Self {
        Self {
            locals: {
                self
                    .locals
                    .into_iter()
                    .zip(other.locals.into_iter())
                    .map(|(x, y)| (x | y).simplify())
                    .collect()
            },
            ..self
        }
    }

    /// Return constrained tuples of operation arguments.
    /// If an operation has args ... t_i ...
    /// where t_i = ... (x_i_j, p_i_j) ...
    /// then the return value should be equivalent to
    /// ... ((... x_i_j ...), (and ... p_i_j ...)) ...
    pub fn args(&self, srcs: &[TempIndex]) -> Disjoints<'ctx, Vec<Value<'ctx>>> {
        srcs
            .iter()
            .map(|idx| self.index(*idx).content.clone().map(|x| vec![x]))
            .fold(
                Disjoints::unit(self.get_ctx()),
                |acc, x| acc.mappend(x)
            )
    }

    pub fn get_ctx(&self) -> &'ctx Context {
        &self.context
    }

    /// Set `var` to empty and return the original values of `var`.
    pub fn del(&mut self, var: TempIndex) -> Disjoints<'ctx, Value<'ctx>> {
        self.index_mut(var).del()
    }

    /// Number of locals.
    pub fn len(&self) -> usize {
        self.locals.len()
    }
}

// traits for LocalMem
use std::ops::{Index, IndexMut};

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

/// Add constraint to each local
impl<'ctx> BitAnd<Constraint<'ctx>> for LocalMemory<'ctx> {
    type Output = Self;

    fn bitand(self, rhs: Constraint<'ctx>) -> Self::Output {
        LocalMemory {
            locals: self.locals.into_iter().map(|x| (x & rhs.clone()).simplify()).collect(),
            ..self
        }
    }
}

impl<'ctx> BitAndAssign<Constraint<'ctx>> for LocalMemory<'ctx> {
    fn bitand_assign(&mut self, rhs: Constraint<'ctx>) {
        for local in &mut self.locals {
            *local &= &rhs;
        }
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