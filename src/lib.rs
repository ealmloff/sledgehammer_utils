use hashbrown::raw::RawTable;
use std::fmt::Debug;
use std::hash::{BuildHasher, Hash, Hasher};
use std::mem::MaybeUninit;

pub struct ConstLru<T, H, const N: usize> {
    entries: MaybeUninit<[Node<T>; N]>,
    free_after: u8,
    first: Option<u8>,
    last: Option<u8>,
    table: RawTable<u8>,
    hasher: H,
}

impl<T: Hash + PartialEq + Debug, H: BuildHasher, const N: usize> Debug for ConstLru<T, H, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConstLru")
            .field("entries", unsafe { self.entries.assume_init_ref() })
            .field("free_after", &self.free_after)
            .field("first", &self.first)
            .field("last", &self.last)
            .finish()
    }
}

impl<T: Hash + PartialEq, H: BuildHasher, const N: usize> ConstLru<T, H, N> {
    pub const fn new(hasher: H) -> Self {
        assert!(N < u8::MAX as usize);
        assert!(N > 0);
        Self {
            entries: MaybeUninit::uninit(),
            free_after: 0,
            first: None,
            last: None,
            table: RawTable::new(),
            hasher,
        }
    }

    pub fn push(&mut self, val: T) -> (u8, bool) {
        let mut hasher = self.hasher.build_hasher();
        val.hash(&mut hasher);
        let hash = hasher.finish();
        if let Some(entry) = self.table.get(hash, |ptr| unsafe {
            self.entries
                .assume_init_ref()
                .get_unchecked(*ptr as usize)
                .data
                == val
        }) {
            unsafe {
                let raw_ptr = self.entries.as_mut_ptr();
                let node = (*raw_ptr).get_unchecked_mut(*entry as usize);
                let next = node.next;
                let prev = node.prev;
                if let Some(next) = next {
                    let next = (*raw_ptr).get_unchecked_mut(next as usize);
                    next.prev = prev;
                }
                if let Some(prev) = prev {
                    let prev = (*raw_ptr).get_unchecked_mut(prev as usize);
                    prev.prev = next;
                }
                if let Some(old_first) = self.first {
                    (*raw_ptr).get_unchecked_mut(old_first as usize).next = Some(*entry);
                }
                self.first = Some(*entry);
                (*entry, false)
            }
        } else {
            let idx = if self.free_after < N as u8 {
                unsafe {
                    *self
                        .entries
                        .assume_init_mut()
                        .get_unchecked_mut(self.free_after as usize) = Node {
                        data: val,
                        next: None,
                        prev: self.first,
                    };
                }
                if let Some(first) = self.first {
                    unsafe {
                        self.entries
                            .assume_init_mut()
                            .get_unchecked_mut(first as usize)
                            .next = Some(self.free_after);
                    }
                }
                self.first = Some(self.free_after);
                if self.last.is_none() {
                    self.last = self.first;
                }
                let idx = self.free_after;
                self.free_after += 1;
                idx
            } else {
                let last = self.last.unwrap();
                let last_node = unsafe {
                    self.entries
                        .assume_init_mut()
                        .get_unchecked_mut(last as usize)
                };
                let new = Node {
                    data: val,
                    next: None,
                    prev: self.first,
                };
                self.last = last_node.next;
                *last_node = new;
                if let Some(last) = self.last {
                    unsafe {
                        self.entries
                            .assume_init_mut()
                            .get_unchecked_mut(last as usize)
                            .prev = None;
                    }
                }
                if let Some(first) = self.first {
                    unsafe {
                        self.entries
                            .assume_init_mut()
                            .get_unchecked_mut(first as usize)
                            .next = Some(last);
                    }
                }
                self.first = Some(last);
                last
            };
            self.table.insert(hash, idx, |ptr| {
                let mut hasher = self.hasher.build_hasher();
                unsafe {
                    self.entries
                        .assume_init_ref()
                        .get_unchecked(*ptr as usize)
                        .data
                        .hash(&mut hasher);
                }
                hasher.finish()
            });
            (idx, true)
        }
    }
}

#[derive(Debug)]
struct Node<T> {
    data: T,
    next: Option<u8>,
    prev: Option<u8>,
}

#[test]
fn push_2() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::*;
    let hash_builder: BuildHasherDefault<DefaultHasher> = BuildHasherDefault::default();
    let mut lru: ConstLru<_, _, 2> = ConstLru::new(hash_builder);
    assert_eq!(lru.push(0), (0, true));
    assert_eq!(lru.push(0), (0, false));
    assert_eq!(lru.push(1), (1, true));
    assert_eq!(lru.push(2), (0, true));
    assert_eq!(lru.push(3), (1, true));
    assert_eq!(lru.push(4), (0, true));
}

#[test]
fn push_100() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::*;
    let hash_builder: BuildHasherDefault<DefaultHasher> = BuildHasherDefault::default();
    let mut lru: ConstLru<_, _, 100> = ConstLru::new(hash_builder);
    for i in 0..100 {
        assert_eq!(lru.push(i), (i as u8, true));
    }
    for i in 0..100 {
        assert_eq!(lru.push(i + 100), (i as u8, true));
    }
}

#[test]
fn sizes() {
    use std::mem::size_of;

    dbg!(size_of::<RawTable<()>>());
    dbg!(size_of::<Node<()>>());
    dbg!(size_of::<ConstLru<(), (), 0>>());
    dbg!(size_of::<ConstLru<(), (), 10>>());
}
