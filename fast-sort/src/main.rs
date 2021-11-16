use rand::prelude::*;
use rand_pcg::Pcg64;
use std::time::{Duration, Instant};
use std::{mem, ptr};

pub mod heap;
pub mod merge;
pub mod partition;
pub mod sortn;

pub use heap::{heap_sort, heap_sort_by};
pub use partition::{quick_sort, quick_sort_by};

#[inline]
pub fn insertion_sort_by<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], is_less: &mut F) {
    if a.len() == 0 {
        return;
    }

    for i in (0..a.len() - 1).rev() {
        insert_head(&mut a[i..], is_less);
    }
}

#[inline]
pub fn insertion_sort<T: Ord>(a: &mut [T]) {
    insertion_sort_by(a, &mut PartialOrd::lt);
}

pub fn insert_head<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], is_less: &mut F) {
    if 2 <= a.len() && is_less(&a[1], &a[0]) {
        unsafe {
            let tmp = mem::ManuallyDrop::new(ptr::read(&a[0]));
            let mut dest: *mut T;

            ptr::copy_nonoverlapping(&a[1], &mut a[0], 1);
            dest = &mut a[1];

            for i in 2..a.len() {
                if !is_less(&a[i], &*tmp) {
                    break;
                }
                ptr::copy_nonoverlapping(&a[i], &mut a[i - 1], 1);
                dest = &mut a[i];
            }

            ptr::copy_nonoverlapping(&*tmp, dest, 1);
        }
    }
}

/// Returns the smallest index `i` such that `key <= a[i]` (`is_less(a[i], key) == false`).
///
/// ONLY WORKS IN A SORTED LIST!
pub fn binary_search_by<T, F: FnMut(&T, &T) -> bool>(key: &T, a: &[T], is_less: &mut F) -> usize {
    let mut size = a.len();
    let mut l = 0;
    let mut r = size;

    while l < r {
        let mid = l + size / 2;

        // SAFETY: the call is made safe by the following invariants:
        // - `mid >= 0`
        // - `mid < size`: `mid` is limited by `[left; right)` bound.
        if is_less(unsafe { a.get_unchecked(mid) }, key) {
            l = mid + 1;
        } else {
            r = mid;
        }

        size = r - l;
    }

    l
}

pub fn merge_sort_by<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], is_less: &mut F) {
    const MAX_INSERTION: usize = 32;

    /// # SAFETY
    /// Same safety as `merge` for `buf`.
    unsafe fn rec<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], buf: *mut T, is_less: &mut F) {
        if a.len() <= MAX_INSERTION {
            insertion_sort_by(a, is_less);
            return;
        }

        let m = a.len() / 2;
        rec(&mut a[..m], buf, is_less);
        rec(&mut a[m..], buf, is_less);

        merge::merge(a, m, buf, is_less);
    }

    if a.len() <= MAX_INSERTION {
        insertion_sort_by(a, is_less);
        return;
    }

    unsafe {
        let mut buf = Vec::with_capacity(a.len() / 2);
        rec(a, buf.as_mut_ptr(), is_less);
    }
}

#[inline]
pub fn merge_sort<T: Ord>(a: &mut [T]) {
    merge_sort_by(a, &mut PartialOrd::lt);
}

pub fn quad_sort_by<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], is_less: &mut F) {
    const MAX_INSERTION: usize = 32;
    const HALF_MEM: bool = false;

    if a.len() <= MAX_INSERTION {
        insertion_sort_by(a, is_less);
        return;
    }

    unsafe {
        let mut buf = Vec::with_capacity(if HALF_MEM { a.len() / 2 } else { a.len() }); // / 2);

        quad_swap(a, is_less);

        // let max_quad_seg_len = a.len() >> 3;
        let mut prev_seg_len = 4;
        let mut seg_len = 16;

        let (body_len, tail_len, mid) = loop {
            let body_len = a.len() & !(seg_len - 1);
            let tail_len = a.len() & (seg_len - 1);

            let mid = {
                let mut res = [prev_seg_len; 3];
                res[0] = prev_seg_len;
                res[1] += prev_seg_len;
                res[2] += res[1];
                res
            };

            if buf.capacity() < seg_len {
                break (body_len, tail_len, mid);
            }

            let mut a_ptr = a.as_mut_ptr();
            let a_body_end = a_ptr.add(body_len);
            while a_ptr < a_body_end {
                merge::quad_merge(
                    std::slice::from_raw_parts_mut(a_ptr, seg_len),
                    mid,
                    buf.as_mut_ptr(),
                    is_less,
                );

                a_ptr = a_ptr.add(seg_len);
            }

            if mid[2] < tail_len {
                merge::quad_merge(
                    std::slice::from_raw_parts_mut(a_body_end, tail_len),
                    mid,
                    buf.as_mut_ptr(),
                    is_less,
                );
            } else if mid[1] < tail_len {
                merge::tri_merge(
                    std::slice::from_raw_parts_mut(a_body_end, tail_len),
                    [mid[0], mid[1]],
                    buf.as_mut_ptr(),
                    is_less,
                );
            } else if mid[0] < tail_len {
                merge::merge(
                    std::slice::from_raw_parts_mut(a_body_end, tail_len),
                    mid[0],
                    buf.as_mut_ptr(),
                    is_less,
                );
            }

            prev_seg_len <<= 2;
            seg_len <<= 2;
        };

        if mid[2] < tail_len {
            if HALF_MEM {
                merge::merge(
                    &mut a[body_len..body_len + mid[1]],
                    mid[0],
                    buf.as_mut_ptr(),
                    is_less,
                );
                merge::merge(
                    &mut a[body_len + mid[1]..],
                    mid[0],
                    buf.as_mut_ptr(),
                    is_less,
                );
                merge::merge(&mut a[body_len..], mid[1], buf.as_mut_ptr(), is_less);
            } else {
                merge::quad_merge(&mut a[body_len..], mid, buf.as_mut_ptr(), is_less);
            }
        } else if mid[1] < tail_len {
            if HALF_MEM {
                merge::merge(
                    &mut a[body_len + mid[0]..],
                    mid[0],
                    buf.as_mut_ptr(),
                    is_less,
                );
                merge::merge(&mut a[body_len..], mid[0], buf.as_mut_ptr(), is_less);
            } else {
                merge::tri_merge(
                    &mut a[body_len..],
                    [mid[0], mid[1]],
                    buf.as_mut_ptr(),
                    is_less,
                );
            }
        } else if mid[0] < tail_len {
            merge::merge(&mut a[body_len..], mid[0], buf.as_mut_ptr(), is_less);
        }

        if 0 < body_len {
            assert_eq!(seg_len, body_len);

            merge::merge(&mut a[..mid[1]], mid[0], buf.as_mut_ptr(), is_less);
            merge::merge(&mut a[mid[1]..body_len], mid[0], buf.as_mut_ptr(), is_less);
            merge::merge(&mut a[..body_len], mid[1], buf.as_mut_ptr(), is_less);

            merge::merge(a, body_len, buf.as_mut_ptr(), is_less);
        }
    }
}
#[inline]
pub fn quad_sort<T: Ord>(a: &mut [T]) {
    quad_sort_by(a, &mut PartialOrd::lt);
}

fn quad_swap<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], is_less: &mut F) {
    let len = a.len();
    let body_len = a.len() & !3;
    let tail_len = len & 3;

    let a = a.as_mut_ptr();

    unsafe {
        for i in (0..body_len).step_by(4) {
            sortn::sort4(a.add(i), is_less);
        }

        if tail_len == 3 {
            sortn::sort3(a.add(body_len), is_less);
        } else if tail_len == 2 {
            sortn::sort2(a.add(body_len), is_less);
        }
    }
}

fn is_sorted_by<T, F: FnMut(&T, &T) -> bool>(a: &[T], is_less: &mut F) -> bool {
    let prev = &a[0];

    for curr in a.iter().skip(1) {
        if is_less(curr, prev) {
            // println!("failed at {}", i);
            // println!("{:?}", a);
            return false;
        }
    }

    true
}

fn is_sorted<T: Ord>(a: &[T]) -> bool {
    is_sorted_by(a, &mut PartialOrd::lt)
}

pub fn timsort_by<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], is_less: &mut F) {
    const MAX_INSERTION: usize = 20;
    const MIN_RUN: usize = 10;

    let len = a.len();

    if len <= MAX_INSERTION {
        insertion_sort_by(a, is_less);
        return;
    }

    let mut buf = Vec::with_capacity(len / 2);

    let mut runs = Vec::new();
    let mut end = len;
    while 0 < end {
        let mut start = end - 1;

        // Find a natural run
        if start > 0 {
            start -= 1;
            unsafe {
                if is_less(a.get_unchecked(start + 1), a.get_unchecked(start)) {
                    // The run is descending
                    while 0 < start && is_less(a.get_unchecked(start), a.get_unchecked(start - 1)) {
                        start -= 1;
                    }
                    a[start..end].reverse();
                } else {
                    // The run is ascending
                    while 0 < start && !is_less(a.get_unchecked(start), a.get_unchecked(start - 1))
                    {
                        start -= 1;
                    }
                }
            }
        }

        // Grow the run if it's too short.
        while 0 < start && end - start < MIN_RUN {
            start -= 1;
            insert_head(&mut a[start..end], is_less)
        }

        runs.push(Run {
            start,
            len: end - start,
        });
        end = start;

        while let Some(i) = collapse(&runs) {
            let l = runs[i + 1];
            let r = runs[i];
            unsafe {
                merge::merge(
                    &mut a[l.start..r.start + r.len],
                    l.len,
                    buf.as_mut_ptr(),
                    is_less,
                );
            }

            runs[i] = Run {
                start: l.start,
                len: l.len + r.len,
            };
            runs.remove(i + 1);
        }
    }

    debug_assert!(runs.len() == 1 && runs[0].start == 0 && runs[0].len == len);

    #[inline]
    fn collapse(runs: &[Run]) -> Option<usize> {
        let n = runs.len();
        if n >= 2
            && (runs[n - 1].start == 0
                || runs[n - 2].len <= runs[n - 1].len
                || (n >= 3 && runs[n - 3].len <= runs[n - 2].len + runs[n - 1].len)
                || (n >= 4 && runs[n - 4].len <= runs[n - 3].len + runs[n - 2].len))
        {
            if n >= 3 && runs[n - 3].len < runs[n - 1].len {
                Some(n - 3)
            } else {
                Some(n - 2)
            }
        } else {
            None
        }
    }

    #[derive(Clone, Copy)]
    struct Run {
        start: usize,
        len: usize,
    }
}

#[inline]
pub fn timsort<T: Ord>(a: &mut [T]) {
    timsort_by(a, &mut PartialOrd::lt);
}

fn test_sort<T: Ord + std::fmt::Debug, R: Rng, F: FnMut(&mut [T])>(
    a: &mut [T],
    rng: &mut R,
    sort: &mut F,
    sort_name: &str,
) {
    let mut time = Duration::from_nanos(0);

    for _ in 0..10 {
        a.shuffle(rng);
        let start = Instant::now();
        sort(a);
        time += start.elapsed();
        assert!(is_sorted(&a));
    }

    println!(
        "{}: {} {} {}",
        sort_name,
        time.as_secs(),
        time.as_millis() % 1000,
        time.as_micros() % 1000,
    );
}

fn main() {
    const TINY_N: usize = 33;
    const SMALL_N: usize = 101;
    const N: usize = 1001;
    const BIG_N: usize = 1000_001;

    let mut rng = Pcg64::from_entropy();

    let mut tiny: Vec<u64> = (0..TINY_N).map(|i| (2 * (i | 1)) as _).collect();
    let mut small: Vec<u64> = (0..SMALL_N).map(|i| (2 * (i | 1)) as _).collect();
    let mut medium: Vec<u64> = (0..N).map(|i| (2 * (i | 1)) as _).collect();
    let mut big: Vec<u64> = (0..BIG_N).map(|i| (2 * (i | 1)) as _).collect();

    assert_eq!(tiny.as_ptr() as usize & 1, 0);
    assert_eq!(small.as_ptr() as usize & 1, 0);
    assert_eq!(medium.as_ptr() as usize & 1, 0);
    assert_eq!(big.as_ptr() as usize & 1, 0);

    println!("# tiny ({})", TINY_N);
    test_sort(&mut tiny, &mut rng, &mut insertion_sort, "insertion_sort");
    test_sort(&mut tiny, &mut rng, &mut <[_]>::sort, "<[_]>::sort");
    test_sort(&mut tiny, &mut rng, &mut quad_sort, "quad_sort");
    test_sort(&mut tiny, &mut rng, &mut merge_sort, "merge_sort");
    test_sort(&mut tiny, &mut rng, &mut timsort, "timsort");
    test_sort(
        &mut tiny,
        &mut rng,
        &mut <[_]>::sort_unstable,
        "<[_]>::sort_unstable",
    );
    test_sort(&mut tiny, &mut rng, &mut heap_sort, "heap_sort");
    test_sort(&mut tiny, &mut rng, &mut quick_sort, "quick_sort");
    println!();

    println!("# small ({})", SMALL_N);
    test_sort(&mut small, &mut rng, &mut insertion_sort, "insertion_sort");
    test_sort(&mut small, &mut rng, &mut <[_]>::sort, "<[_]>::sort");
    test_sort(&mut small, &mut rng, &mut quad_sort, "quad_sort");
    test_sort(&mut small, &mut rng, &mut merge_sort, "merge_sort");
    test_sort(&mut small, &mut rng, &mut timsort, "timsort");
    test_sort(
        &mut small,
        &mut rng,
        &mut <[_]>::sort_unstable,
        "<[_]>::sort_unstable",
    );
    test_sort(&mut small, &mut rng, &mut heap_sort, "heap_sort");
    test_sort(&mut small, &mut rng, &mut quick_sort, "quick_sort");
    println!();

    println!("# medium ({})", N);
    test_sort(&mut medium, &mut rng, &mut insertion_sort, "insertion_sort");
    test_sort(&mut medium, &mut rng, &mut <[_]>::sort, "<[_]>::sort");
    test_sort(&mut medium, &mut rng, &mut quad_sort, "quad_sort");
    test_sort(&mut medium, &mut rng, &mut merge_sort, "merge_sort");
    test_sort(&mut medium, &mut rng, &mut timsort, "timsort");
    test_sort(
        &mut medium,
        &mut rng,
        &mut <[_]>::sort_unstable,
        "<[_]>::sort_unstable",
    );
    test_sort(&mut medium, &mut rng, &mut heap_sort, "heap_sort");
    test_sort(&mut medium, &mut rng, &mut quick_sort, "quick_sort");
    println!();

    println!("# big ({})", BIG_N);
    test_sort(&mut big, &mut rng, &mut <[_]>::sort, "<[_]>::sort");
    test_sort(&mut big, &mut rng, &mut quad_sort, "quad_sort");
    test_sort(&mut big, &mut rng, &mut merge_sort, "merge_sort");
    test_sort(&mut big, &mut rng, &mut timsort, "timsort");
    test_sort(
        &mut big,
        &mut rng,
        &mut <[_]>::sort_unstable,
        "<[_]>::sort_unstable",
    );
    test_sort(&mut big, &mut rng, &mut heap_sort, "heap_sort");
    test_sort(&mut big, &mut rng, &mut quick_sort, "quick_sort");
    println!();
}
