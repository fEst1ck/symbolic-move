pub trait Functor {
    /// The `a` in `F a`
    type Source;

    /// The `F b` in `F a -> F b`
    type Fb<B>: Functor<Source=B>;

    fn map<B, F>(self, f: F) -> Self::Fb<B>
        where F: Fn(Self::Source) -> B + Clone;
}

pub trait Monoidal: Functor + Sized {
    fn unit() -> Self::Fb<()>;

    fn prod<B: Clone>(self, other: Self::Fb<B>) -> Self::Fb<(Self::Source, B)>;

    fn lift_a2<F, B: Clone, C>(self, another: Self::Fb<B>, f: F)
    -> <<Self as Functor>::Fb<(<Self as Functor>::Source, B)> as Functor>::Fb<C>
        where F: Fn(Self::Source, B) -> C
    {
        self.prod(another)
        .map(|(x, y)| f(x, y))
    }
}

// impl<T: Applicative> Monoidal for T {
//     fn unit() -> Self::Fb<()> {
//         Self::pure(())
//     }

//     fn prod<B>(self, other: Self::Fb<B>) -> Self::Fb<(Self::Source, B)> {
//         self.map(|x: Self::Source| (|y: B| (x, y)))
//             .ap(other)
//     }
// }

pub trait Applicative: Functor + Sized {
    fn pure(x: Self::Source) -> Self;

    fn ap<B, F>(self, f: Self::Fb<F>) -> Self::Fb<B>
        where F: Fn(Self::Source) -> B + Clone;
}

// impl<T: Monoidal> Applicative for T {
//     fn pure(x: Self::Source) -> Self {
//         Self::unit().map(|_: ()| x)
//     }

//     fn ap<B, F>(self, f: Self::Fb<F>) -> Self::Fb<B>
//         where F: Fn(Self::Source) -> B
//     {
//         f.prod(self)
//          .map(|(f, a)| f(a))    
//     }
// }

pub trait Monad: Applicative {
    fn ret(x: Self::Source) -> Self {
        Self::pure(x)
    }

    fn bind<B, F>(self, f: F) -> Self::Fb<B>
        where F: Fn(Self::Source) -> Self::Fb<B> + Clone;
}

pub trait Monoid {
    fn mappend(self, other: Self) -> Self;
}

impl<T> Monoid for Vec<T> {
    fn mappend(self, other: Self) -> Self {
        self.append(&mut other);
        self
    }
}