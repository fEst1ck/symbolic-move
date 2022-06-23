use crate::traits::{Functor, Monoidal, Applicative};

pub enum SymbolicTree<OrderedConstraint: Ord, Val> {
    Node(Val),
    Leaf(Box<Self>, OrderedConstraint, Box<Self>)
}

impl<OrderedConstraint: Ord, Val> Functor for SymbolicTree<OrderedConstraint, Val> {
    type Source = Val;
    type Fb<U> = SymbolicTree<OrderedConstraint, U>;

    fn map<B, F>(self, f: F) -> Self::Fb<B>
            where F: Fn(Self::Source) -> B + Clone
    {
        match self {
            SymbolicTree::Node(v) => SymbolicTree::Node(f(v)),
            SymbolicTree::Leaf(l, p, r) => {
                SymbolicTree::Leaf(Box::new(l.map(f.clone())), p, Box::new(r.map(f.clone())))
            }
        }
    }
}

impl<OrderedConstraint: Ord + Clone, Val: Clone> Monoidal for SymbolicTree<OrderedConstraint, Val> {
    fn unit() -> Self::Fb<()> {
        SymbolicTree::Node(())
    }

    fn prod<B: Clone>(self, other: Self::Fb<B>) -> Self::Fb<(Self::Source, B)> {
        use SymbolicTree::*;
        match (self, other) {
            (Node(v1), Node(v2)) => Node((v1, v2)),
            (t1@Node(_), Leaf(l, p, r)) => {
                Leaf(Box::new(t1.clone().prod(*l)), p, Box::new(t1.prod(*r)))
            }
            (Leaf(l, p, r), t2@Node(_)) => {
                Leaf(Box::new(l.prod(t2.clone())), p, Box::new(r.prod(t2)))
            }
            (Leaf(l1, p1, r1), Leaf(l2, p2, r2)) => {
                match p1.cmp(&p2) {
                    std::cmp::Ordering::Less => {
                        let t1 = Leaf(l1, p1, r1);
                        Leaf(Box::new(t1.clone().prod(*l2)), p2, Box::new(t1.prod(*r2)))
                    },
                    std::cmp::Ordering::Equal => Leaf(Box::new(l1.prod(*l2)), p1, Box::new(r1.prod(*r2))),
                    std::cmp::Ordering::Greater => {
                        let t2 = Leaf(l2, p2, r2);
                        Leaf(Box::new(l1.prod(t2.clone())), p1, Box::new(r1.prod(t2)))
                    },
                }
            }
        }
    }
}

impl<OrderedConstraint: Ord + Clone, Val: Clone> Applicative for SymbolicTree<OrderedConstraint, Val> {
    fn pure(x: Self::Source) -> Self {
        // Self::unit().map(|_: ()| x)
        SymbolicTree::Node(x)
    }

    fn ap<B, F>(self, f: Self::Fb<F>) -> SymbolicTree<OrderedConstraint, B>
        where F: Clone + Fn(Val) -> B
    {
        f.prod(self)
         .map(|(f, a)| f(a))
    }
}

impl<OrderedConstraint: Ord + Clone, Val: Clone> Clone for SymbolicTree<OrderedConstraint, Val> {
    fn clone(&self) -> Self {
        use SymbolicTree::*;
        match self {
            Node(v) => Node(v.clone()),
            Leaf(l, p, r) => Leaf(l.clone(), p.clone(), r.clone())
        }
    }
}