use std::marker::PhantomData;

pub(crate) trait Key: Copy { fn new(index: usize) -> Self; fn index(self) -> usize; }
macro_rules! key {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub(crate) struct $name(usize);
        impl crate::arena::Key for $name {
            fn new(index: usize) -> Self { Self(index) }
            fn index(self) -> usize { self.0 }
        }
    };
}
pub(crate) use key;

#[derive(Debug)]
pub(crate) struct Arena<K, T> { data: Vec<T>, key: PhantomData<K> }
impl<K, T> Default for Arena<K, T> {
    fn default() -> Self { Self { data: Vec::new(), key: PhantomData } }
}
impl<K: Key, T> Arena<K, T> {
    pub fn alloc(&mut self, value: T) -> K {
        let key = K::new(self.data.len()); self.data.push(value); key
    }
    pub fn get(&self, key: K) -> &T { &self.data[key.index()] }
    pub fn len(&self) -> usize { self.data.len() }
    pub fn bytes(&self) -> usize { self.data.capacity() * std::mem::size_of::<T>() }
}
