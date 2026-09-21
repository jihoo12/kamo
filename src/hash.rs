//! Non-cryptographic hashing for internal arena IDs and structural node keys.
//! Source-level names continue to use the standard randomized string hasher.
use std::hash::{BuildHasherDefault, Hasher};

pub(crate) type IdMap<K, V> = std::collections::HashMap<K, V, BuildHasherDefault<IdHasher>>;
pub(crate) struct IdHasher(u64);
impl Default for IdHasher {
    fn default() -> Self {
        Self(0xcbf29ce484222325)
    }
}
impl Hasher for IdHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for chunk in &mut chunks {
            self.write_u64(u64::from_ne_bytes(chunk.try_into().unwrap()));
        }
        for byte in chunks.remainder() {
            self.write_u8(*byte);
        }
    }
    fn write_u64(&mut self, value: u64) {
        self.0 = (self.0 ^ value).wrapping_mul(0x100000001b3);
    }
    fn write_usize(&mut self, value: usize) {
        self.write_u64(value as u64);
    }
    fn write_u32(&mut self, value: u32) {
        self.write_u64(value as u64);
    }
    fn write_u8(&mut self, value: u8) {
        self.write_u64(value as u64);
    }
}
