use std::{
    fmt::{self, Display},
    ops::{BitAnd, BitAndAssign}, cmp::Ordering,
};

use z3::{
    ast::{Ast, Bool},
    Context, SatResult, Solver,
};

use crate::{traits::{Functor, Monoidal, Applicative}, context::global_context};

/// Boolean sort
pub type Constraint<'ctx> = Bool<'ctx>;

#[derive(Debug, Clone)]
pub struct OrderedConstraint<'ctx> {
    time_stamp: usize,
    pub constraint: Constraint<'ctx>
}

impl<'ctx> PartialEq for OrderedConstraint<'ctx> {
    fn eq(&self, other: &Self) -> bool {
        self.time_stamp == other.time_stamp
    }
}

impl<'ctx> Eq for OrderedConstraint<'ctx> {}

impl<'ctx> PartialOrd for OrderedConstraint<'ctx> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.time_stamp.partial_cmp(&other.time_stamp)
    }
}

impl<'ctx> Ord for OrderedConstraint<'ctx> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.time_stamp.cmp(&other.time_stamp)
    }
}

/// Return false if the constraint is unsatisfiable.
pub fn sat<'ctx>(constraint: &Constraint<'ctx>) -> bool {
    let solver = Solver::new(constraint.get_ctx());
    solver.assert(constraint);
    match solver.check() {
        SatResult::Unsat => false,
        _ => true,
    }
}

/// Return `None` if the constraint is unsatisfiable, else the wrapped value.
pub fn constraint_filter<'ctx>(constraint: Constraint<'ctx>) -> Option<Constraint<'ctx>> {
    if sat(&constraint) {
        Some(constraint)
    } else {
        None
    }
}

// Single Constrained Value ////////////////////////////////////////////////

/// Simple guarded expression.
pub struct Constrained<'ctx, T> {
    pub content: T,
    pub constraint: Constraint<'ctx>,
}

impl<'ctx, T> Constrained<'ctx, T> {
    pub fn get_ctx(self) -> &'ctx Context {
        self.constraint.get_ctx()
    }
}

/// The (_, Constrained) functor
impl<'ctx, T> Functor for Constrained<'ctx, T> {
    type Source = T;
    type Fb<U> = Constrained<'ctx, U>;

    fn map<B, F>(self, f: F) -> Self::Fb<B>
            where F: Fn(Self::Source) -> B
    {
      Constrained {
        content: f(self.content),
        constraint: self.constraint,
      }
    }
}

impl<T> Monoidal for Constrained<'static, T> {
    fn unit() -> Self::Fb<()> {
        Constrained {
            content: (),
            constraint: Bool::from_bool(global_context(), true),
        }
    }

    fn prod<B>(self, other: Self::Fb<B>) -> Self::Fb<(Self::Source, B)> {
        Constrained {
            content: (self.content, other.content),
            constraint: self.constraint & other.constraint
        }
    }
}

impl<T: Clone> Applicative for Constrained<'static, T> {
    fn pure(x: Self::Source) -> Self {
        // Self::unit().map(|_: ()| x)
        Constrained {
            content: x,
            constraint: Bool::from_bool(global_context(), true),
        }
    }

    fn ap<B, F>(self, f: Self::Fb<F>) -> Constrained<'static, B>
        where F: Fn(T) -> B
    {
        f.prod(self)
         .map(|(f, a)| f(a))
    }
}

impl<'ctx, T: Clone> Clone for Constrained<'ctx, T> {
    fn clone(&self) -> Self {
        Self {
            content: self.content.clone(),
            constraint: self.constraint.clone(),
        }
    }
}

/// Impose another constraint.
impl<'ctx, T> BitAnd<Bool<'ctx>> for Constrained<'ctx, T> {
    type Output = Self;

    fn bitand(self, rhs: Bool<'ctx>) -> Self::Output {
        Constrained {
            constraint: self.constraint & rhs,
            ..self
        }
    }
}

impl<'ctx, T> BitAnd<&Bool<'ctx>> for Constrained<'ctx, T> {
    type Output = Self;

    fn bitand(self, rhs: &Bool<'ctx>) -> Self::Output {
        Constrained {
            constraint: self.constraint & rhs,
            ..self
        }
    }
}

impl<'ctx, T> BitAndAssign<Bool<'ctx>> for Constrained<'ctx, T> {
    fn bitand_assign(&mut self, rhs: Bool<'ctx>) {
        self.constraint &= rhs;
    }
}

impl<'ctx, T> BitAndAssign<&Bool<'ctx>> for Constrained<'ctx, T> {
    fn bitand_assign(&mut self, rhs: &Bool<'ctx>) {
        self.constraint &= rhs;
    }
}

impl<'ctx, T: PartialEq> PartialEq for Constrained<'ctx, T> {
    fn eq(&self, other: &Self) -> bool {
        self.content == other.content && self.constraint == other.constraint
    }
}

impl<'ctx, T: Display> Display for Constrained<'ctx, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} ↩ {})", self.content, self.constraint)
    }
}