use std::fmt::Debug;
use std::hash::{BuildHasher, Hash, Hasher};
use std::mem::MaybeUninit;

struct RawTable<T, const N: usize> {
    buckets: [Option<T>; N],
}

impl<T: Copy, const N: usize> RawTable<T, N> {
    const fn new() -> Self {
        Self { buckets: [None; N] }
    }

    fn get(&self, hash: u64, mut eq: impl FnMut(&T) -> bool) -> Option<&T> {
        let mut offset = 0;
        loop {
            let index = (hash as usize + offset) % N;
            println!("index: {} {} {}", index, N, offset * offset);
            let val = unsafe { self.buckets.get_unchecked(index).as_ref() };
            if let Some(val) = val {
                if eq(val) {
                    return Some(val);
                }
            } else {
                return None;
            }
            offset += 1;
        }
    }

    fn insert(&mut self, hash: u64, value: T) {
        let mut offset = 0;
        loop {
            let index = (hash as usize + offset) % N;
            let val = unsafe { self.buckets.get_unchecked_mut(index) };
            if val.is_none() {
                *val = Some(value);
                return;
            }
            offset += 1;
        }
    }
}

pub struct ConstLru<T, H, const N: usize, const N2: usize> {
    entries: MaybeUninit<[Node<T>; N]>,
    free_after: u8,
    first: Option<u8>,
    last: Option<u8>,
    table: RawTable<u8, N2>,
    hasher: H,
}

impl<T: Hash + PartialEq + Debug, H: BuildHasher, const N: usize, const N2: usize> Debug
    for ConstLru<T, H, N, N2>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConstLru")
            .field("entries", unsafe { self.entries.assume_init_ref() })
            .field("free_after", &self.free_after)
            .field("first", &self.first)
            .field("last", &self.last)
            .finish()
    }
}

impl<T: Hash + PartialEq, H: BuildHasher, const N: usize, const N2: usize> ConstLru<T, H, N, N2> {
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
                self.table.insert(hash, idx);
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
    let mut lru: ConstLru<_, _, 2, 4> = ConstLru::new(hash_builder);
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
    let mut lru: ConstLru<_, _, 100, 200> = ConstLru::new(hash_builder);
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

    dbg!(size_of::<RawTable<u8, 0>>());
    dbg!(size_of::<RawTable<u8, 10>>());
    dbg!(size_of::<RawTable<u8, 128>>());
    dbg!(size_of::<Node<()>>());
    dbg!(size_of::<ConstLru<(), (), 0, 0>>());
    dbg!(size_of::<ConstLru<(), (), 10, 20>>());
    dbg!(size_of::<ConstLru<u8, (), 128, 256>>());
}
