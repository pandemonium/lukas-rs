//! The compiler's hash maps, and the hasher they use.
//!
//! Names are the compiler's keys: a `QualifiedName` is a module path and a
//! member, all of it `String`, and every variable occurrence looks one up.
//! `std`'s default hasher is SipHash-1-3, chosen to keep a server's maps safe
//! from an adversary picking colliding keys -- a threat a compiler reading a
//! source file does not have, and a profile of a check spent 30% of its time
//! paying for it.
//!
//! This is the hasher rustc uses for the same reason: a multiply-and-rotate over
//! the input, which for the short strings and small integers that make up a name
//! is a few instructions rather than a keyed permutation. It also has no random
//! seed, so iteration order is at least the same from run to run.

use std::hash::{BuildHasherDefault, Hasher};

/// Maps and sets keyed by names, type variables, and other compiler-internal
/// keys. Use `default()` rather than `new()`: `new` exists only for `RandomState`.
pub type HashMap<K, V> = std::collections::HashMap<K, V, BuildHasherDefault<FxHasher>>;
pub type HashSet<T> = std::collections::HashSet<T, BuildHasherDefault<FxHasher>>;

/// A constant with a well-mixed bit pattern; the multiplication is what carries
/// each input word's influence up into the high bits.
const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;

#[derive(Debug, Default, Clone, Copy)]
pub struct FxHasher {
    hash: u64,
}

impl FxHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(5) ^ word).wrapping_mul(SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut rest = bytes;
        while let Some((word, tail)) = rest.split_first_chunk::<8>() {
            self.add(u64::from_le_bytes(*word));
            rest = tail;
        }
        if let Some((half, tail)) = rest.split_first_chunk::<4>() {
            self.add(u64::from(u32::from_le_bytes(*half)));
            rest = tail;
        }
        for &byte in rest {
            self.add(u64::from(byte));
        }
    }

    #[inline]
    fn write_u8(&mut self, value: u8) {
        self.add(u64::from(value));
    }

    #[inline]
    fn write_u16(&mut self, value: u16) {
        self.add(u64::from(value));
    }

    #[inline]
    fn write_u32(&mut self, value: u32) {
        self.add(u64::from(value));
    }

    #[inline]
    fn write_u64(&mut self, value: u64) {
        self.add(value);
    }

    #[inline]
    fn write_usize(&mut self, value: usize) {
        self.add(value as u64);
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::Hash;

    fn hash_of<A: Hash>(value: &A) -> u64 {
        let mut hasher = FxHasher::default();
        value.hash(&mut hasher);
        hasher.finish()
    }

    /// The point of a hash: equal keys agree, and keys that differ anywhere --
    /// including in a byte past the first word -- do not.
    #[test]
    fn names_that_differ_hash_differently() {
        assert_eq!(hash_of(&"Stdlib.Data.List"), hash_of(&"Stdlib.Data.List"));
        assert_ne!(hash_of(&"Stdlib.Data.List"), hash_of(&"Stdlib.Data.Lisp"));
        assert_ne!(hash_of(&"fold_left"), hash_of(&"fold_right"));
        assert_ne!(hash_of(&1u32), hash_of(&2u32));
    }

    /// A map of every short name a program might use, with no key lost to a
    /// collision the map could not resolve.
    #[test]
    fn a_map_keyed_by_names_finds_them_all() {
        let names = (0..2000)
            .map(|n| format!("Stdlib.Data.List.item_{n}"))
            .collect::<Vec<_>>();
        let map = names
            .iter()
            .enumerate()
            .map(|(n, name)| (name.clone(), n))
            .collect::<HashMap<_, _>>();

        assert_eq!(map.len(), names.len());
        for (n, name) in names.iter().enumerate() {
            assert_eq!(map.get(name), Some(&n));
        }
    }
}
