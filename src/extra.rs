use crate::mapping::{AddError, RankMapping};
use crate::{GrowableMapping, Mapping};
use std::convert::Infallible;
use std::error::Error;
use std::marker::PhantomData;

pub trait Extra<T>: Sized {
    type ConstructErr: Error;

    fn construct(elems: impl IntoIterator<Item = T>) -> Result<Self, Self::ConstructErr>;
}

pub trait AddExtra<T>: Extra<T> {
    type AddErr: Error;

    fn add(&mut self, elem: T) -> Result<(), Self::AddErr>;
}

impl<T> Extra<T> for () {
    type ConstructErr = Infallible;

    fn construct(_elems: impl IntoIterator<Item = T>) -> Result<Self, Self::ConstructErr> {
        Ok(())
    }
}

impl<T> AddExtra<T> for () {
    type AddErr = Infallible;

    fn add(&mut self, _elem: T) -> Result<(), Self::AddErr> {
        Ok(())
    }
}

pub struct ByRank<M, T> {
    mapping: M,
    phantom: PhantomData<T>,
}

impl<M, T> ByRank<M, T>
where
    M: Mapping<T, usize>,
{
    pub fn rank(&self, elem: &T) -> Option<usize> {
        self.mapping.get(elem).copied()
    }

    pub fn set_rank(&mut self, elem: T, rank: usize) {
        self.mapping.set(elem, rank)
    }
}

impl<M, T> Extra<T> for ByRank<M, T>
where
    M: RankMapping<T>,
{
    type ConstructErr = <M as RankMapping<T>>::Err;

    fn construct(elems: impl IntoIterator<Item = T>) -> Result<Self, Self::ConstructErr> {
        Ok(Self {
            mapping: M::zero_map(elems)?,
            phantom: Default::default(),
        })
    }
}

impl<M, T> AddExtra<T> for ByRank<M, T>
where
    M: GrowableMapping<T, usize>,
{
    type AddErr = AddError;

    fn add(&mut self, elem: T) -> Result<(), Self::AddErr> {
        let length = self.mapping.len();
        self.mapping.add(elem, length + 1)
    }
}
