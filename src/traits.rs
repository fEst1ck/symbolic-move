#![feature(generic_associated_types)]

trait Functor {
    /// The `a` in `F a`
    type A;

    /// The `F b` in `F a -> F b`
    type Fb<B>: Functor<Source=B>;

    fn map<B, F>(self, f: F) -> Self::Fb<B>
        where F: Fn(Self::A) -> B;
}

trait Monoidal: Functor {
    fn unit() -> Self::Fb<()>;

    fn prod<B>(self, other: Fb<B>) -> Self::Fb<(Self::A, B)>;
}

impl<T: Applicative> Monoidal for T {
    fn unit() -> Self::Fb<()> {
        pure(())
    }

    fn prod<B>(self, other: Fb<B>) -> Self::Fb<(Self::A, B)> {
        self.map(|x: Self::A| (|y: B| (x, y)))
            .ap(other)
    }
}

trait Applicative: Functor {
    fn pure(x: Self::A) -> Self;

    fn ap<B>(f: Self::Fb(F)) -> Fb(B)
        where F: Fn(Self::A) -> B;
}

impl<T: Monoidal> Applicative for T {
    fn pure(x: Self::A) -> Self {
        unit().map(|_| x)
    }

    fn ap<B>(f: Self::Fb(F)) -> Fb(B)
        where F: Fn(Self::A) -> B
    {
        f.prod(self)
         .map(|(f, a)| f(a))    
    }
}