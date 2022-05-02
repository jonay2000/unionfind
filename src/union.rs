pub trait Union<T> {
    type Err;

    fn union(&self, a: &T, b: &T) -> Result<T, Self::Err>;
}

impl<F, T, E> Union<T> for F
where
    F: Fn(&T, &T) -> Result<T, E>,
{
    type Err = E;

    fn union(&self, a: &T, b: &T) -> Result<T, Self::Err> {
        (self)(a, b)
    }
}
