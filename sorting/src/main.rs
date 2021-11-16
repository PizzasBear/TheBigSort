#![allow(dead_code)]

use rand::prelude::*;
use std::time::Instant;
use std::{cmp, mem};

fn insertion_sort(a: &mut [u32]) {
    for i in 0..a.len() {
        for j in (0..i).rev() {
            if a[j + 1] < a[j] {
                a.swap(j, j + 1);
            } else {
                break;
            }
        }
    }
}

fn binary_insertion_sort(a: &mut [u32]) {
    for i in 0..a.len() {
        let j = match binary_search(&a[..i], a[i]) {
            Ok(j) => j,
            Err(j) => j,
        };
        if j < i {
            a[j..=i].rotate_right(1);
        }
    }
}

fn binary_search(a: &[u32], s: u32) -> Result<usize, usize> {
    let mut low = 0;
    let mut high = a.len();
    while low < high {
        let mid = (low + high) / 2;
        if a[mid] < s {
            low = mid + 1;
        } else if a[mid] == s {
            return Ok(mid);
        } else {
            high = mid;
        }
    }
    Err(low)
}

fn merge_sort(a: &mut [u32]) {
    #[inline]
    fn merge(a: &[u32], b: &[u32], out: &mut [u32]) {
        let mut i = 0;
        let mut j = 0;
        while i < a.len() && j < b.len() {
            if b[j] < a[i] {
                out[i + j] = b[j];
                j += 1;
            } else {
                out[i + j] = a[i];
                i += 1;
            }
        }
        while j < b.len() {
            out[i + j] = b[j];
            j += 1;
        }
        while i < a.len() {
            out[i + j] = a[i];
            i += 1;
        }
    }

    const MAX_INSERTIONS: usize = 20;
    if a.len() < MAX_INSERTIONS {
        insertion_sort(a);
        return;
    }
    let mut b = vec![0; a.len()].into_boxed_slice();
    let mut width = MAX_INSERTIONS;
    for i in (0..a.len()).step_by(width) {
        let n = cmp::min(a.len(), i + width);
        insertion_sort(&mut a[i..n]);
    }
    while width < a.len() {
        for i in (0..a.len()).step_by(2 * width) {
            let n = cmp::min(a.len(), i + width);
            let m = cmp::min(a.len(), i + 2 * width);
            if n == m {
                break;
            }
            merge(&a[i..n], &a[n..m], &mut b);
            a[i..m].copy_from_slice(&b[..m - i])
        }
        width *= 2;
    }
}

fn quick_sort(a: &mut [u32]) {
    #[inline]
    fn choose_pivot(a: &mut [u32]) -> usize {
        const SHORTEST_MEDIAN_OF_MEDIANS: usize = 50;

        let mut i = a.len() / 4;
        let mut j = a.len() / 2;
        let mut k = i + j;

        if 8 <= a.len() {
            let sort2 = |i: &mut _, j: &mut usize| {
                if a[*j] < a[*i] {
                    mem::swap(i, j);
                }
            };
            let sort3 = |i: &mut usize, j: &mut usize, k: &mut usize| {
                sort2(i, j);
                sort2(j, k);
                sort2(i, j);
            };

            if SHORTEST_MEDIAN_OF_MEDIANS < a.len() {
                let sort_adjacent = |i: &mut usize| {
                    sort3(&mut (*i - 1), i, &mut (*i + 1));
                };
                sort_adjacent(&mut i);
                sort_adjacent(&mut j);
                sort_adjacent(&mut k);
            }

            sort3(&mut i, &mut j, &mut k);
        }

        j
    }

    #[inline]
    fn partition(a: &mut [u32], p: usize) -> usize {
        let mut low = 0;
        let mut high = a.len();
        while low < high {
            if a[p] < a[low] {
                if high == p + 1 {
                    high -= 2;
                } else {
                    high -= 1;
                }
                a.swap(low, high);
            } else {
                low += 1;
            }
        }
        low
    }

    const MAX_INSERTIONS: usize = 20;
    if a.len() < MAX_INSERTIONS {
        insertion_sort(a);
        return;
    }
    let p = choose_pivot(a);
    let sep = partition(a, p);
    if sep < p {
        a.swap(p, sep);
        quick_sort(&mut a[..sep]);
        quick_sort(&mut a[sep + 1..]);
    } else {
        a.swap(p, sep - 1);
        quick_sort(&mut a[..sep - 1]);
        quick_sort(&mut a[sep..]);
    }
}

fn heap_sort(a: &mut [u32]) {
    #[inline]
    fn sift_down(a: &mut [u32], mut root: usize) {
        loop {
            let left = root * 2 + 1;
            let right = left + 1;
            let greater = if right < a.len() && a[left] < a[right] {
                right
            } else {
                left
            };

            if a.len() <= greater || a[greater] < a[root] {
                return;
            }

            a.swap(greater, root);
            root = greater;
        }
    }

    const MAX_INSERTIONS: usize = 20;
    if a.len() < MAX_INSERTIONS {
        insertion_sort(a);
        return;
    }
    // heapify
    for i in (0..a.len() / 2).rev() {
        sift_down(a, i);
    }
    for i in (1..a.len()).rev() {
        a.swap(0, i);
        sift_down(&mut a[..i], 0);
    }
}

fn radix256_sort(original_ref: &mut [u32]) {
    let mut a = original_ref;

    let mut out_vec = vec![0; a.len()];
    let mut out = out_vec.as_mut_slice();

    for digit_i in 0..4usize {
        let shift = digit_i * 8;
        let mut counter = [0; 256];
        for n in a.iter().copied() {
            let digit = (n as usize >> shift) & 0xff;
            counter[digit] += 1;
        }
        for i in 1..counter.len() {
            counter[i] += counter[i - 1];
        }
        for n in a.iter().copied().rev() {
            let digit = (n as usize >> shift) & 0xff;
            counter[digit] -= 1;
            out[counter[digit]] = n;
        }
        let tmp = a;
        a = out;
        out = tmp;
    }
}

fn check_sorted(a: &[u32]) -> bool {
    for i in 1..a.len() {
        if a[i] < a[i - 1] {
            return false;
        }
    }
    true
}

fn fmt_num(n: u128) -> String {
    let mut s = n.to_string();
    // 10000
    // 10_000
    let mut i = s.len();
    while 4 < i {
        i -= 3;
        s.insert(i, '_');
    }
    s
}

const A_SIZES: &[usize] = &[
    10,
    100,
    1000,
    10_000,
    100_000,
    1000_000,
    10_000_000,
    100_000_000,
    // 1000_000_000,
];
const NUM_TESTS: u128 = 2;

const FUNCS: &[fn(&mut [u32])] = &[
    insertion_sort,
    binary_insertion_sort,
    merge_sort,
    quick_sort,
    heap_sort,
    radix256_sort,
    <[u32]>::sort,
    <[u32]>::sort_unstable,
];
const ALGO_NAMES: &[&str] = &[
    "insertion_sort",
    "binary_insertion_sort",
    "merge sort",
    "quick sort",
    "heap sort",
    "radix256 sort",
    "rust sort",
    "rust unstable sort",
];

fn main() {
    debug_assert_eq!(FUNCS.len(), ALGO_NAMES.len());

    let a = &mut [9, 2, 8, 5, 6, 3, 7, 1, 4][..];
    binary_insertion_sort(a);
    println!("{:?}", a);

    let mut rng = SmallRng::from_entropy();
    for n in A_SIZES.iter().copied() {
        let mut times = [0; FUNCS.len()];
        for _ in 0..NUM_TESTS {
            for (i, func) in FUNCS.iter().enumerate() {
                let mut a = (0..n).map(|_| rng.gen()).collect::<Box<[u32]>>();
                let now = Instant::now();
                func(&mut a);
                times[i] += now.elapsed().as_nanos();
                if !check_sorted(&mut a) {
                    panic!("{} failed!", ALGO_NAMES[i]);
                }
            }
        }

        for time in times.iter_mut() {
            *time /= NUM_TESTS;
        }
        let mut min_time = *times.iter().min().unwrap();
        let mut units = "nanos";
        if 3000 < min_time {
            min_time /= 1000;
            for time in times.iter_mut() {
                *time /= 1000;
            }
            units = "micros";
        }
        if 3000 < min_time {
            min_time /= 1000;
            for time in times.iter_mut() {
                *time /= 1000;
            }
            units = "millis";
        }
        if 3000 < min_time {
            for time in times.iter_mut() {
                *time /= 1000;
            }
            units = "secs";
        }

        println!("n = {}:", fmt_num(n as _));
        for i in 0..FUNCS.len() {
            println!("\t{} = {} {}", ALGO_NAMES[i], fmt_num(times[i]), units);
        }
    }
    println!("Hello, world!");
}
