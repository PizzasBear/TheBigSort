use crate::binary_search_by;
use std::{mem, ptr};

#[inline]
pub unsafe fn left_child<T>(a: *const T, node: *const T) -> *const T {
    ((2 * node as usize - a as usize) as *const T).add(1)
}
#[inline]
pub unsafe fn left_child_mut<T>(a: *mut T, node: *mut T) -> *mut T {
    left_child(a, node) as _
}

#[inline]
pub unsafe fn parent<T>(a: *const T, node: *const T) -> *const T {
    a.add((node.offset_from(a) as usize - 1) / 2)
}
#[inline]
pub unsafe fn parent_mut<T>(a: *mut T, node: *mut T) -> *mut T {
    parent(a, node) as _
}

#[inline]
pub fn heap_sort_by<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], is_less: &mut F) {
    heapify(a, &mut |a, b| is_less(b, a));
    for i in (0..a.len()).rev() {
        a.swap(0, i);
        sift_down(&mut a[..i], 0, &mut |a, b| is_less(b, a));
    }
}

#[inline]
pub fn heap_sort<T: Ord>(a: &mut [T]) {
    heap_sort_by(a, &mut PartialOrd::lt);
}

#[inline]
pub fn heapify<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], is_less: &mut F) {
    for i in (0..a.len() / 2).rev() {
        sift_down(a, i, is_less);
    }
}

pub fn sift_down<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], i: usize, is_less: &mut F) {
    unsafe {
        let len = a.len();
        let a = a.as_mut_ptr();
        let a_end = a.add(len);

        let mut node = a.add(i);

        loop {
            let left_child = left_child_mut(a, node);
            let right_child = left_child.add(1);

            if right_child < a_end {
                let min = if is_less(&*right_child, &*left_child) {
                    right_child
                } else {
                    left_child
                };

                if is_less(&*node, &*min) {
                    break;
                } else {
                    ptr::swap(min, node);
                    node = min;
                }
            } else if right_child == a_end {
                if is_less(&*left_child, &*node) {
                    ptr::swap(left_child, node);
                }
                break;
            } else {
                break;
            }
        }
    }
}

pub unsafe fn saving_leaf_search<T, F: FnMut(&T, &T) -> bool>(
    a: &[T],
    i: usize,
    mut buf: *mut *const T,
    is_less: &mut F,
) -> *mut *const T {
    let len = a.len();
    let a = a.as_ptr();
    let a_end = a.add(len);

    let mut node = a.add(i);

    loop {
        *buf = node;
        buf = buf.add(1);

        let left_child = left_child(a, node);
        let right_child = left_child.add(1);

        if right_child < a_end {
            node = if is_less(&*right_child, &*left_child) {
                right_child
            } else {
                left_child
            };
        } else if right_child == a_end {
            *buf = left_child;
            break buf.add(1);
        } else {
            break buf;
        }
    }
}

pub fn leaf_search<T, F: FnMut(&T, &T) -> bool>(a: &[T], i: usize, is_less: &mut F) -> *const T {
    unsafe {
        let len = a.len();
        let a = a.as_ptr();
        let a_end = a.add(len);

        let mut node = a.add(i);

        loop {
            let left_child = left_child(a, node);
            let right_child = left_child.add(1);

            if right_child < a_end {
                node = if is_less(&*right_child, &*left_child) {
                    right_child
                } else {
                    left_child
                };
            } else if right_child == a_end {
                break left_child;
            } else {
                break node;
            }
        }
    }
}

/// Just like `sift_down`, but with less comparisons.
pub fn bounce_sift_down<T, F: FnMut(&T, &T) -> bool>(a: &mut [T], i: usize, is_less: &mut F) {
    unsafe {
        let mut swap_node = leaf_search(a, i, is_less) as *mut _;
        let a = a.as_mut_ptr();
        let node = a.add(i);

        loop {
            if swap_node == node {
                return;
            } else if !is_less(&*node, &*swap_node) {
                break;
            } else {
                swap_node = parent_mut(a, swap_node);
            }
        }

        let mut x = mem::ManuallyDrop::new(ptr::read(swap_node));
        ptr::copy_nonoverlapping(node, swap_node, 1);

        while node < swap_node {
            swap_node = parent_mut(a, swap_node);
            ptr::swap(&mut *x, swap_node);
        }
    }
}

/// Just like `sift_down`, but with less comparisons.
pub fn saving_bounce_sift_down<T, F: FnMut(&T, &T) -> bool>(
    a: &mut [T],
    i: usize,
    is_less: &mut F,
) {
    unsafe {
        const MAX_DEPTH: usize = 8 * mem::size_of::<usize>();

        let mut buf = mem::MaybeUninit::<[*const T; MAX_DEPTH]>::uninit().assume_init();
        let buf_len = saving_leaf_search(a, i, buf.as_mut_ptr(), is_less)
            .offset_from(buf.as_mut_ptr()) as usize;

        let a = a.as_mut_ptr();
        let node = a.add(i);

        let mut swap_node =
            buf[binary_search_by(&(node as *const _), &buf[1..buf_len], &mut |a, b| {
                !is_less(&**b, &**a)
            })] as *mut _;

        // loop {
        //     if swap_node == node {
        //         return;
        //     } else if !is_less(&*node, &*swap_node) {
        //         break;
        //     } else {
        //         swap_node = parent_mut(a, swap_node);
        //     }
        // }

        let mut x = mem::ManuallyDrop::new(ptr::read(swap_node));
        ptr::copy_nonoverlapping(node, swap_node, 1);

        while node < swap_node {
            swap_node = parent_mut(a, swap_node);
            ptr::swap(&mut *x, swap_node);
        }
    }
}
