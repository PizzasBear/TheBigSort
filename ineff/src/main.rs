// #![feature(linked_list_cursors)]

use std::io::Write;
use std::str::FromStr;
use std::time::Instant;

use rand::prelude::*;
use rand_pcg::Pcg64;

/// Quickly checks if the given array is sorted. Notable for being used for bogosort, but excluded
/// from bogobogosort.
///
/// O(n)
pub fn is_sorted<T: Ord>(a: &[T]) -> bool {
    a[1..]
        .iter()
        .try_fold(&a[0], |prev, x| if *x < *prev { None } else { Some(x) })
        .is_some()
}

/// Why????
///
/// O(n! ^ n)
pub fn bogobogosort<T: Ord + Copy, R: Rng>(a: &mut [T], rng: &mut R) {
    if a.len() < 2 {
        return;
    }
    loop {
        let mut b = a.iter().copied().collect::<Box<[_]>>();
        loop {
            bogobogosort(&mut b[1..], rng);
            if b[0] < b[1] {
                break;
            } else {
                b.shuffle(rng);
            }
        }
        if a.iter().zip(b.iter()).all(|(&a, &b)| a == b) {
            break;
        } else {
            a.shuffle(rng);
        }
    }
}

/// A Monkey on a Typewriter. He will get it right eventually.
///
/// O(n!)
pub fn bogosort<T: Ord, R: Rng>(a: &mut [T], rng: &mut R) {
    while !is_sorted(a) {
        a.shuffle(rng);
    }
}

/// Divide and Conquer! Yeah!
///
/// O(n ^ log n)
pub fn slow_sort<T: Ord>(a: &mut [T]) {
    if a.len() < 2 {
        return;
    } else {
        let m = a.len() / 2;
        slow_sort(&mut a[..m]);
        slow_sort(&mut a[m..]);
        if a[m] < a[0] {
            a.swap(0, m);
        }
        slow_sort(&mut a[1..]);
    }
}

/// FAST, runs in POLY-TIME.
///
/// O(n ^ (log 3 / log 1.5))
pub fn stooge_sort<T: Ord>(a: &mut [T]) {
    if a.len() < 2 {
        return;
    } else {
        let l = a.len();
        if a[l - 1] < a[0] {
            a.swap(0, a.len() - 1);
        }
        if 2 < a.len() {
            let t = l / 3;
            stooge_sort(&mut a[..l - t]);
            stooge_sort(&mut a[t..]);
            stooge_sort(&mut a[..l - t]);
        }
    }
}

/// A classic old algorithm, usually it has the title of a slow sorting algorithm. But its faster
/// than any of the algorithms above.
///
/// O(n ^ 2)
pub fn bubble_sort<T: Ord>(a: &mut [T]) {
    for i in (2..=a.len()).rev() {
        for j in 1..i {
            if a[j] < a[j - 1] {
                a.swap(j, j - 1);
            }
        }
    }
}

pub fn selection_sort<T: Ord>(a: &mut [T]) {
    for i in 0..a.len() - 1 {
        let mut min = i;
        for j in i + 1..a.len() {
            if a[j] < a[min] {
                min = j;
            }
        }
        a.swap(i, min);
    }
}

pub fn double_selection_sort<T: Ord>(a: &mut [T]) {
    for i in 0..a.len() / 2 {
        let j = a.len() - i - 1;
        let mut min = i;
        let mut max = i;
        for k in i + 1..=j {
            if a[k] < a[min] {
                min = k;
            } else if a[max] < a[k] {
                max = k;
            }
        }
        if max == i {
            if min == j {
                a.swap(i, j);
            } else {
                a.swap(i, j);
                a.swap(i, min);
            }
        } else {
            a.swap(i, min);
            a.swap(j, max);
        }
    }
}

/// The fastest algorithm of the squared saga.
///
/// O(n ^ 2)
pub fn insertion_sort<T: Ord>(a: &mut [T]) {
    for i in 1..a.len() {
        insert_head(a, i);
    }
}

// /// The fastest algorithm of the squared saga.
// ///
// /// O(n ^ 2)
// pub fn ada_insertion_sort<T: Ord>(a: &mut [T]) {
//     let mut m = 0;
//     for i in 1..a.len() {
//         if a[i] < a[m] {
//             insert_tail(a, i);
//         }
//         insert_head(a, i);
//     }
// }

/// O(n)
pub fn insert_tail<T: Ord>(a: &mut [T], mut i: usize) {
    while i + 1 < a.len() {
        if a[i] > a[i + 1] {
            a.swap(i, i + 1);
            i += 1;
        } else {
            break;
        }
    }
}

/// O(n)
pub fn insert_head<T: Ord>(a: &mut [T], mut i: usize) {
    while 0 < i {
        if a[i - 1] > a[i] {
            a.swap(i - 1, i);
            i -= 1;
        } else {
            break;
        }
    }
}

pub fn sift_down<T: Ord>(a: &mut [T], start: usize, end: usize) {
    let mut root = start;
    let mut child = 2 * start + 2;
    while child < end {
        if a[child] < a[child - 1] {
            child -= 1;
        }

        if a[child] <= a[root] {
            return;
        }

        a.swap(root, child);
        root = child;
        child = 2 * root + 2;
    }
    if child == end && a[root] < a[child - 1] {
        a.swap(root, child - 1);
    }
}

/// Turns any array into a binary max heap.
pub fn heapify<T: Ord>(a: &mut [T]) {
    for i in (0..=(a.len() - 2) / 2).rev() {
        sift_down(a, i, a.len());
    }
}

/// A classic in place "fast" unstable comparison sort algorithm. It uses a binary max heap to
/// find the maximum of the array and puts it at the end.
///
/// O(n log n)
pub fn heap_sort<T: Ord>(a: &mut [T]) {
    heapify(a);
    for i in (1..a.len()).rev() {
        a.swap(0, i);
        sift_down(a, 0, i);
    }
}

/// A quick algorithm that merges two sorted arrays into one.
///
/// O(n + m)
pub fn merge<T: Ord + Copy>(a: &[T], b: &[T], out: &mut [T]) {
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        if a[i] < b[j] {
            out[i + j] = a[i];
            i += 1;
        } else {
            out[i + j] = b[j];
            j += 1;
        }
    }
    while i < a.len() {
        out[i + j] = a[i];
        i += 1;
    }
    while j < b.len() {
        out[i + j] = b[j];
        j += 1;
    }
}

/// Recursively merges sub-lists with each other in order to get the whole list sorted. It
/// inspired slow-sort.
///
/// O(n log n)
pub fn merge_sort<T: Ord + Copy + Default>(a: &mut [T]) {
    const MERGE_SORT_MIN_LEN: usize = 32;
    fn merge_sort_rec1<T: Ord + Copy>(a: &mut [T], buf: &mut [T]) {
        if MERGE_SORT_MIN_LEN < a.len() {
            let m = a.len() / 2;
            if MERGE_SORT_MIN_LEN < m {
                merge_sort_rec2(&mut a[..m], &mut buf[..m]);
                merge_sort_rec2(&mut a[m..], &mut buf[m..]);
                merge(&buf[..m], &buf[m..], a);
            } else {
                insertion_sort(&mut a[..m]);
                insertion_sort(&mut a[m..]);
                tim_merge(a, m, buf);
            }
        } else {
            insertion_sort(a)
        }
    }
    fn merge_sort_rec2<T: Ord + Copy>(a: &mut [T], buf: &mut [T]) {
        if 1 < a.len() {
            let m = a.len() / 2;
            merge_sort_rec1(&mut a[..m], &mut buf[..m]);
            merge_sort_rec1(&mut a[m..], &mut buf[m..]);
            merge(&a[..m], &a[m..], buf);
        }
    }
    merge_sort_rec1(a, &mut vec![Default::default(); a.len()]);
}

/// An optimized, less general version of merge from merge-sort. Used in tim-sort.
///
/// O(n)
pub fn tim_merge<T: Ord + Copy>(a: &mut [T], mid: usize, buf: &mut [T]) {
    if mid <= a.len() - mid {
        buf[..mid].copy_from_slice(&a[..mid]);
        let mut left = 0; // buf index
        let mut right = mid; // a index
        let mut out = 0; // a index

        while left < mid && right < a.len() {
            a[out] = if a[right] < buf[left] {
                right += 1;
                a[right - 1]
            } else {
                left += 1;
                buf[left - 1]
            };
            out += 1;
        }

        a[out..right].copy_from_slice(&buf[left..mid]);
    } else {
        buf[..a.len() - mid].copy_from_slice(&a[mid..]);
        let mut left = mid; // a index
        let mut right = a.len() - mid; // buf index
        let mut out = a.len(); // a index

        while 0 < left && 0 < right {
            out -= 1;
            a[out] = if buf[right - 1] < a[left - 1] {
                left -= 1;
                a[left]
            } else {
                right -= 1;
                buf[right]
            }
        }

        a[left..out].copy_from_slice(&buf[..right])
    }
}

pub fn tim_sort<T: Ord + Copy + Default>(a: &mut [T]) {
    use std::ops::Range;
    const TIM_SORT_MIN_LEN: usize = 32;
    if a.len() <= TIM_SORT_MIN_LEN {
        insertion_sort(a);
        return;
    }
    let mut buf = vec![T::default(); a.len() / 2];
    let mut runs = Vec::new();
    let mut end = a.len();
    while 0 < end {
        let mut start = end - 1;
        if 0 < start {
            start -= 1;
            if a[start] <= a[start + 1] {
                while 1 < start && a[start - 1] <= a[start] {
                    start -= 1;
                }
            } else {
                while 1 < start && a[start - 1] >= a[start] {
                    start -= 1;
                }
                a[start..end].reverse();
            }
        }
        while 0 < start && end - start < TIM_SORT_MIN_LEN {
            start -= 1;
            insert_tail(&mut a[start..end], 0);
        }
        runs.push(start..end);
        assert!(is_sorted(&a[start..end]));
        end = start;

        while let Some(r) = collapse(&runs) {
            let left = runs[r + 1].clone();
            let right = runs[r].clone();
            // merge(&a[left.clone()], &a[right.clone()], &mut buf);
            runs[r] = left.start..right.end;
            assert!(is_sorted(&a[left.clone()]));
            assert!(is_sorted(&a[right.clone()]));
            tim_merge(&mut a[runs[r].clone()], left.len(), &mut buf);
            assert!(is_sorted(&a[runs[r].clone()]));
            runs.remove(r + 1);
        }
    }

    #[inline]
    fn collapse(runs: &[Range<usize>]) -> Option<usize> {
        let n = runs.len();
        if n >= 2
            && (runs[n - 1].start == 0
                || runs[n - 2].len() <= runs[n - 1].len()
                || (n >= 3 && runs[n - 3].len() <= runs[n - 2].len() + runs[n - 1].len())
                || (n >= 4 && runs[n - 4].len() <= runs[n - 3].len() + runs[n - 2].len()))
        {
            if n >= 3 && runs[n - 3].len() < runs[n - 1].len() {
                Some(n - 3)
            } else {
                Some(n - 2)
            }
        } else {
            None
        }
    }
}

#[inline]
pub fn sort2<T: Ord>(a: [&mut T; 2]) {
    use std::ptr;
    if *a[1] < *a[0] {
        unsafe {
            let tmp = ptr::read(a[0]);
            *a[0] = ptr::read(a[1]);
            *a[1] = tmp;
        }
    }
}

#[inline]
pub fn sort3<T: Ord>([a0, a1, a2]: [&mut T; 3]) {
    sort2([a0, a1]);
    sort2([a1, a2]);
    sort2([a0, a1]);
}

#[inline]
pub fn sort4<T: Ord>(a: [&mut T; 4]) {
    use std::ptr;
    unsafe {
        let [tmp0, tmp1, tmp2, tmp3]: [T; 4];

        if *a[0] > *a[1] {
            tmp0 = ptr::read(a[1]);
            tmp1 = ptr::read(a[0]);
        } else {
            tmp0 = ptr::read(a[0]);
            tmp1 = ptr::read(a[1]);
        }

        if *a[2] > *a[3] {
            tmp2 = ptr::read(a[3]);
            tmp3 = ptr::read(a[2]);
        } else {
            tmp2 = ptr::read(a[2]);
            tmp3 = ptr::read(a[3]);
        }

        if tmp1 <= tmp2 {
            *a[0] = tmp0;
            *a[1] = tmp1;
            *a[2] = tmp2;
            *a[3] = tmp3;
        } else if tmp0 > tmp3 {
            *a[0] = tmp2;
            *a[1] = tmp3;
            *a[2] = tmp0;
            *a[3] = tmp1;
        } else {
            if tmp0 <= tmp2 {
                *a[0] = tmp0;
                *a[1] = tmp2;
            } else {
                *a[0] = tmp2;
                *a[1] = tmp0;
            }

            if tmp1 <= tmp3 {
                *a[2] = tmp1;
                *a[3] = tmp3;
            } else {
                *a[2] = tmp3;
                *a[3] = tmp1;
            }
        }
    }
}

/// Partitions the array. It's the heart of quick sort.
///
/// O(n)
pub fn partition<T: Ord>(a: &mut [T], p: &T) -> usize {
    let mut i = 0;
    let mut j = a.len();
    loop {
        while a[i] <= *p {
            i += 1;
            if i == a.len() {
                return a.len();
            }
        }
        loop {
            if j == 0 {
                return 0;
            }
            j -= 1;
            if a[j] < *p {
                break;
            }
        }
        if j <= i {
            // a.swap(j, 0);
            return i;
        }
        a.swap(i, j);
        i += 1;
    }
}

// #[test]
// fn partition_min_max_p() {
//     let mut a = (20..=40).collect::<Box<[_]>>();
//     a.shuffle(&mut thread_rng());
//     println!("    {:?}", a);
//     println!("{:02}, {:?}", partition(&mut a, &80), a);
//     println!("{:02}, {:?}", partition(&mut a, &0), a);
//     println!("{:02}, {:?}", partition(&mut a, &30), a);
// }

/// A more optimized version of partition. It uses way less branching and utilizes cache better.
///
/// O(n)
pub fn block_partition<T: Ord>(a: &mut [T], p: &T) -> usize {
    const BUF_SIZE: u8 = 32; // 64;
    let mut buf_i = [0u8; BUF_SIZE as usize];
    let mut buf_j = [0u8; BUF_SIZE as usize];

    let mut i = 0;
    let mut j = a.len();
    let mut start_i = 0;
    let mut start_j = 0;
    let mut num_i = 0;
    let mut num_j = 0;
    while j - i > 2 * BUF_SIZE as usize {
        if num_i == 0 {
            start_i = 0;
            for k in 0..BUF_SIZE {
                buf_i[num_i] = k;
                num_i += (*p < a[i + k as usize]) as usize;
            }
        }
        if num_j == 0 {
            start_j = 0;
            for k in 1..=BUF_SIZE {
                buf_j[num_j] = k;
                num_j += (a[j - k as usize] < *p) as usize;
            }
        }
        let num = num_i.min(num_j);
        for k in 0..num {
            a.swap(
                i + buf_i[start_i + k] as usize,
                j - buf_j[start_j + k] as usize,
            );
        }
        num_i -= num;
        num_j -= num;
        start_i += num;
        start_j += num;
        if num_i == 0 {
            i += BUF_SIZE as usize;
        }
        if num_j == 0 {
            j -= BUF_SIZE as usize;
        }
    }
    partition(&mut a[i..j], p) + i
}

/// Quickly guesses the median of an array. It isn't that accurate but its better than just taking
/// the middle of the array
///
/// O(1)
pub fn choose_pivot<T: Ord>(a: &[T]) -> usize {
    use std::mem::swap;

    let len = a.len();
    // let mut num_swaps = 0;
    let sort2 = |i: &mut usize, j: &mut usize| {
        if a[*j] < a[*i] {
            swap(i, j);
            // num_swaps += 1;
        }
    };
    let sort3 = |i: &mut usize, j: &mut usize, k: &mut usize| {
        // stooge sort
        sort2(i, j);
        sort2(j, k);
        sort2(i, j);
    };
    let sort_adj = |i: &mut usize| sort3(&mut (*i - 1), i, &mut (*i + 1));
    let mut i = len / 4 * 1;
    let mut j = len / 4 * 2;
    let mut k = len / 4 * 3;

    if 50 <= len {
        sort_adj(&mut i);
        sort_adj(&mut j);
        sort_adj(&mut k);
    }
    sort3(&mut i, &mut j, &mut k);
    j
}

/// The fastest classic comparison sorting algorithm known.
///
/// best & normal case: O(n log n)
/// worst case: O(n ^ 2)
pub fn quick_sort<T: Ord>(a: &mut [T]) {
    const QUICK_SORT_MIN_LEN: usize = 24;
    if a.len() < QUICK_SORT_MIN_LEN {
        insertion_sort(a)
    } else {
        let p = choose_pivot(a);
        a.swap(0, p);
        let (p, b) = a.split_first_mut().unwrap();
        let m = partition(b, p) + 1;
        if m < a.len() - m {
            quick_sort(&mut a[..m]);
            quick_sort(&mut a[m..]);
        } else {
            quick_sort(&mut a[m..]);
            quick_sort(&mut a[..m]);
        }
    }
}

/// Combining Quick Sort and Heap Sort to make a more stable sorting algorithm. It uses
/// non-required additional optimizations like block-partition.
///
/// O(n log n)
pub fn intro_sort<T: Ord>(a: &mut [T]) {
    const INTRO_SORT_MIN_LEN: usize = 24;

    let log_len = 8 * std::mem::size_of::<usize>() - a.len().leading_zeros() as usize;
    rec(a, 2 * log_len);
    insertion_sort(a);

    fn rec<T: Ord>(a: &mut [T], depth: usize) {
        if a.len() < INTRO_SORT_MIN_LEN {
            // insertion_sort(a);
        } else if depth == 0 {
            heap_sort(a);
        } else {
            let p = choose_pivot(a);
            a.swap(0, p);
            let (p, b) = a.split_first_mut().unwrap();
            let m = block_partition(b, p) + 1;
            if m < a.len() - m {
                rec(&mut a[..m], depth - 1);
                rec(&mut a[m..], depth - 1);
            } else {
                rec(&mut a[m..], depth - 1);
                rec(&mut a[..m], depth - 1);
            }
        }
    }
}

type RadixSortUint = u64;

/// One of the only sorting algorithms in O(n) time that works on u64.
/// O(n)
pub fn radix_sort(a: &mut [RadixSortUint]) {
    use std::mem::{size_of, swap};

    const DIGIT_BITS: usize = 1 << 3;
    const NUM_DIGITS: usize = 8 * size_of::<RadixSortUint>() / DIGIT_BITS;

    let mut buf = vec![0; a.len()];

    let mut from = a;
    let mut to = buf.as_mut_slice();
    for i in 0..NUM_DIGITS {
        let mut count = [0; 1 << DIGIT_BITS];
        for &n in from.iter() {
            count[get_digit(n, i)] += 1;
        }
        for j in 1..count.len() {
            count[j] += count[j - 1];
        }
        for &n in from.iter().rev() {
            let d = get_digit(n, i);
            count[d] -= 1;
            to[count[d]] = n;
        }
        swap(&mut from, &mut to);
    }
    if NUM_DIGITS & 1 == 1 {
        from.copy_from_slice(to);
    }

    #[inline(always)]
    fn get_digit(n: RadixSortUint, digit_idx: usize) -> usize {
        ((n >> digit_idx * DIGIT_BITS) & ((1 << DIGIT_BITS) - 1)) as _
    }
}

/// An in-place imporvement of strand sort. A weird merge sort.
/// Looks like a strange version of patience sort.
///
/// best case: O(n log n)
/// worst case: O(n ^ 2)
pub fn my_strand_sort<T: Ord + Copy + Default>(a: &mut [T]) {
    const MY_STRAND_SORT_MIN_LEN: usize = 20;

    fn rec<T: Ord + Copy>(a: &mut [T], buf: &mut [T]) {
        if a.len() < MY_STRAND_SORT_MIN_LEN {
            insertion_sort(a);
            return;
        }
        let mut i = 1;
        let mut j = a.len();
        'partition_loop: loop {
            while a[i - 1] <= a[i] {
                i += 1;
                if i == a.len() {
                    break 'partition_loop;
                }
            }
            loop {
                if j == 0 {
                    break 'partition_loop;
                }
                j -= 1;
                if a[i - 1] <= a[j] {
                    break;
                }
            }
            if j <= i {
                break 'partition_loop;
            }
            a.swap(i, j);
            i += 1;
        }
        rec(&mut a[i..], buf);
        tim_merge(a, i, buf);
    }

    let mut buf = vec![T::default(); a.len() / 2];
    rec(a, &mut buf);
}

pub fn patience_sort<T: Ord + Copy>(a: &mut [T]) {
    use std::cmp::{Ordering, Reverse};
    use std::collections::BinaryHeap;

    struct PrioritizedElement<T: Ord> {
        val: Reverse<T>,
        pile: usize,
    }
    impl<T: Ord> PartialEq for PrioritizedElement<T> {
        fn eq(&self, other: &Self) -> bool {
            self.val.eq(&other.val)
        }
    }
    impl<T: Ord> Eq for PrioritizedElement<T> {}
    impl<T: Ord> PartialOrd for PrioritizedElement<T> {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    impl<T: Ord> Ord for PrioritizedElement<T> {
        fn cmp(&self, other: &Self) -> Ordering {
            self.val.cmp(&other.val)
        }
    }

    let mut piles: Vec<Vec<_>> = vec![];
    for &n in a.iter() {
        match piles.binary_search_by_key(&n, |pile| *pile.last().unwrap()) {
            Ok(i) => piles[i].push(n),
            Err(i) => {
                if i == a.len() {
                    piles.push(vec![n]);
                } else {
                    piles[i].push(n);
                }
            }
        }
    }
    let mut heap = BinaryHeap::with_capacity(piles.len());
    for (_, pile) in piles.iter_mut().enumerate() {
        heap.push(pile.pop());
    }
}

fn read<T: FromStr>(buf: &mut String, name: &str) -> Result<T, T::Err> {
    buf.clear();
    print!("{}: ", name);
    std::io::stdout().flush().unwrap();
    std::io::stdin().read_line(buf).unwrap();
    buf.pop();
    T::from_str(&buf)
}

fn main() {
    let mut rng = Pcg64::from_entropy();
    let mut buf = String::new();

    let n = read::<u64>(&mut buf, "size of the array").unwrap_or(100000);
    let iterations = read::<u64>(&mut buf, "number of iterations").unwrap_or(100);
    let mut a = (0..n).collect::<Box<_>>();
    a.shuffle(&mut rng);

    if n <= 20 {
        println!("{:?}", a);
    }
    let s = read::<String>(&mut buf, "the algorithm").unwrap();
    let mut micros = 0;
    let mut count = 0;
    for _ in 0..iterations {
        let start = Instant::now();
        match s.to_lowercase().as_str() {
            "bogobogosort" | "bogo bogo sort" | "bogobogo" | "bogo bogo" => {
                bogobogosort(&mut a, &mut rng)
            }
            "bogosort" | "bogo sort" | "bogo" => bogosort(&mut a, &mut rng),
            "slowsort" | "slow sort" | "slow" => slow_sort(&mut a),
            "stoogesort" | "stooge sort" | "stooge" => stooge_sort(&mut a),
            "bubblesort" | "bubble sort" | "bubble" => bubble_sort(&mut a),
            "selectionsort" | "selection sort" | "selection" | "sel" => selection_sort(&mut a),
            "doubleselectionsort"
            | "double selection sort"
            | "doubleselection"
            | "double selection"
            | "dselection"
            | "dsel" => double_selection_sort(&mut a),
            "insertionsort" | "insertion sort" | "insertion" | "ins" => insertion_sort(&mut a),
            "heapsort" | "heap sort" | "heap" => heap_sort(&mut a),
            "mergesort" | "merge sort" | "merge" => merge_sort(&mut a),
            "timsort" | "tim sort" | "tim" => tim_sort(&mut a),
            "quicksort" | "quick sort" | "quick" => quick_sort(&mut a),
            "introsort" | "intro sort" | "intro" => intro_sort(&mut a),
            "stdsort" | "std sort" | "std" => a.sort(),
            "stdunstablesort" | "std unstable sort" | "stdunstable" | "std unstable" | "stdu" => {
                a.sort_unstable()
            }
            "radixsort" | "radix sort" | "radix" => radix_sort(&mut a),
            "mystrandsort" | "my strand sort" | "mystrand" | "my strand" | "strand" => {
                my_strand_sort(&mut a)
            }
            _ => {
                println!("{}", s);
                unimplemented!()
            }
        }
        micros += start.elapsed().as_micros();
        assert!(is_sorted(&a), "{:?}", a);
        a.shuffle(&mut rng);
        count += 1;
    }
    println!(
        "timed {}.{:03} for {} runs",
        micros / 1000,
        micros % 1000,
        count
    );
}
