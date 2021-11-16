use crate::{heap_sort_by, insertion_sort_by, sortn::sort3};
use std::{mem, ptr};

#[inline]
pub fn quick_sort_by<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], is_less: &mut F) {
    const INSERTION_MAX: usize = 32;

    fn rec<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], depth: u32, is_less: &mut F) {
        if a.len() <= INSERTION_MAX {
            insertion_sort_by(a, is_less);
        } else if depth == 0 {
            heap_sort_by(a, is_less);
        } else {
            let pivot_idx = choose_pivot(a, is_less);
            a.swap(0, pivot_idx);

            let (pivot, tail) = a.split_first_mut().unwrap();
            let mid = block_partition(tail, pivot, is_less) + 1;

            if mid < a.len() - mid {
                rec(&mut a[..mid], depth - 1, is_less);
                rec(&mut a[mid..], depth - 1, is_less);
            } else {
                rec(&mut a[mid..], depth - 1, is_less);
                rec(&mut a[..mid], depth - 1, is_less);
            }
        }
    }

    let log_len = usize::BITS - a.len().leading_zeros();
    rec(a, 2 * log_len, is_less);
}

#[inline]
pub fn quick_sort<T: Ord>(a: &mut [T]) {
    quick_sort_by(a, &mut PartialOrd::lt);
}

pub fn choose_pivot<T, F: FnMut(&T, &T) -> bool>(a: &[T], is_less: &mut F) -> usize {
    if a.len() < 16 {
        a.len() / 2
    } else {
        let mut idx = [a.len() / 4, a.len() / 2, 3 * a.len() / 4];

        if 64 < a.len() {
            for i in idx.iter_mut() {
                let mut adj_idx = [*i - 1, *i, *i + 1];
                unsafe {
                    sort3(adj_idx.as_mut_ptr(), &mut |&i, &j| is_less(&a[i], &a[j]));
                }
                *i = adj_idx[1];
            }
        }

        unsafe {
            sort3(idx.as_mut_ptr(), &mut |&i, &j| is_less(&a[i], &a[j]));
        }
        idx[1]
    }
}

pub fn partition<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], pivot: &T, is_less: &mut F) -> usize {
    if a.is_empty() {
        return 0;
    }

    unsafe {
        let len = a.len();
        let a = a.as_mut_ptr();
        let a_end = a.add(len);

        let mut left = a;
        let mut right = a_end;
        loop {
            while left < right && is_less(&*left, pivot) {
                left = left.add(1);
            }
            while left < right && !is_less(&*right.sub(1), pivot) {
                right = right.sub(1);
            }
            if right <= left {
                break;
            }
            right = right.sub(1);
            ptr::swap(left, right);
            left = left.add(1);
        }
        // 'main_loop: loop {
        //     while is_less(&*left, pivot) {
        //         left = left.add(1);
        //         if left == a_end {
        //             break 'main_loop;
        //         }
        //     }
        //     loop {
        //         if right == a {
        //             break 'main_loop;
        //         }
        //         right = right.sub(1);
        //         if !is_less(pivot, &*right) {
        //             break;
        //         }
        //     }
        //     if right <= left {
        //         break;
        //     }
        //     ptr::swap(left, right);
        //     left = left.add(1);
        // }

        left.offset_from(a) as _
    }
}

pub fn block_partition<T, F: FnMut(&T, &T) -> bool>(
    a: &mut [T],
    pivot: &T,
    is_less: &mut F,
) -> usize {
    const BLOCK: usize = 32;

    unsafe {
        let mut offsets_l = [mem::MaybeUninit::<u8>::uninit(); BLOCK];
        let mut offsets_r = [mem::MaybeUninit::<u8>::uninit(); BLOCK];

        let (mut start_l, mut start_r) = (0, 0);
        let (mut num_l, mut num_r) = (0, 0);

        let mut l = 0;
        let mut r = a.len();

        // while l < r && is_less(&*l, pivot) {
        //     l = l.add(1);
        // }
        // while l < r && !is_less(&*r.sub(1), pivot) {
        //     r = r.sub(1);
        // }
        // if r <= l {
        //     return l.offset_from(a) as _;
        // }

        while 2 * BLOCK < r - l {
            if num_l == 0 {
                start_l = 0;
                for i in 0..BLOCK {
                    *offsets_l.get_unchecked_mut(num_l) = mem::MaybeUninit::new(i as _);
                    num_l += !is_less(a.get_unchecked(l + i), pivot) as usize;
                }
            }
            if num_r == 0 {
                start_r = 0;
                for i in 1..=BLOCK {
                    *offsets_r.get_unchecked_mut(num_r) = mem::MaybeUninit::new(i as _);
                    num_r += !is_less(pivot, a.get_unchecked(r - i)) as usize;
                }
            }

            let num = num_l.min(num_r);
            for i in 0..num {
                ptr::swap(
                    a.get_unchecked_mut(
                        l + offsets_l.get_unchecked(start_l + i).assume_init() as usize,
                    ),
                    a.get_unchecked_mut(
                        r - offsets_r.get_unchecked(start_r + i).assume_init() as usize,
                    ),
                );
            }

            num_l -= num;
            num_r -= num;
            start_l += num;
            start_r += num;

            if num_l == 0 {
                l += BLOCK;
            }
            if num_r == 0 {
                r -= BLOCK;
            }
        }

        l + partition(&mut a[l..r], pivot, is_less)
    }
}
// pub fn block_partition<T, F: FnMut(&T, &T) -> bool>(
//     a: &mut [T],
//     pivot: &T,
//     is_less: &mut F,
// ) -> usize {
//     const BLOCK: usize = 32;
//
//     unsafe {
//         let mut offsets_l = [mem::MaybeUninit::<u8>::uninit(); BLOCK];
//         let mut offsets_r = [mem::MaybeUninit::<u8>::uninit(); BLOCK];
//
//         let (mut start_l, mut start_r) = (0, 0);
//         let (mut num_l, mut num_r) = (0, 0);
//
//         let len = a.len();
//         let a = a.as_mut_ptr();
//         let a_end = a.add(len);
//
//         let mut l = a;
//         let mut r = a_end;
//
//         // while l < r && is_less(&*l, pivot) {
//         //     l = l.add(1);
//         // }
//         // while l < r && !is_less(&*r.sub(1), pivot) {
//         //     r = r.sub(1);
//         // }
//         // if r <= l {
//         //     return l.offset_from(a) as _;
//         // }
//
//         while 2 * BLOCK < r.offset_from(l) as usize {
//             if num_l == 0 {
//                 start_l = 0;
//                 for i in 0..BLOCK {
//                     *offsets_l.get_unchecked_mut(num_l) = mem::MaybeUninit::new(i as _);
//                     num_l += !is_less(&*l.add(i), pivot) as usize;
//                 }
//             }
//             if num_r == 0 {
//                 start_r = 0;
//                 for i in 1..=BLOCK {
//                     *offsets_r.get_unchecked_mut(num_r) = mem::MaybeUninit::new(i as _);
//                     num_r += !is_less(pivot, &*r.sub(i)) as usize;
//                 }
//             }
//
//             let num = num_l.min(num_r);
//             for i in 0..num {
//                 ptr::swap(
//                     l.add(offsets_l.get_unchecked(start_l + i).assume_init() as _),
//                     r.sub(offsets_r.get_unchecked(start_r + i).assume_init() as _),
//                 );
//             }
//
//             num_l -= num;
//             num_r -= num;
//             start_l += num;
//             start_r += num;
//
//             if num_l == 0 {
//                 l = l.add(BLOCK);
//             }
//             if num_r == 0 {
//                 r = r.sub(BLOCK);
//             }
//         }
//
//         partition(
//             slice::from_raw_parts_mut(l, r.offset_from(l) as usize),
//             pivot,
//             is_less,
//         ) + l.offset_from(a) as usize
//     }
// }
