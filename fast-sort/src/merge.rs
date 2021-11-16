use crate::binary_search_by;
use std::ptr;

/// Merges two consecutive sorted runs together. The first run's length is `m`, and the second run starts at `m`.
/// This function doesn't read from `buf`, so it is safe and recomended to reuse `buf` for multiple merges.
///
/// # SAFETY
/// Don't read from `buf` since it will contain a partial shallow copy of `a` after the execution.
/// Make sure that `a[..m]` and `a[m..]` are sorted, so that nothing wierd happens.
///
/// # Panics
/// This function will panic when m is outside the range `0..=a.len()`.
/// Or if `buf` is not big enough to perform the merge (This won't panic if `buf.len()` is at least `a.len() / 2`).
pub unsafe fn merge<T, F: FnMut(&T, &T) -> bool>(
    a: &mut [T],
    mid: usize,
    buf: *mut T,
    is_less: &mut F,
) {
    assert!((0..=a.len()).contains(&mid));
    if mid == 0 || mid == a.len() {
        return;
    }

    let len = a.len();
    let a = a.as_mut_ptr();
    let (a_mid, a_end) = (a.add(mid), a.add(len));

    if !is_less(&*a_mid, &*a_mid.sub(1)) {
        return;
    }

    // Chooses whether to "move" the left or the right half of `a` into `buf`.
    if mid <= len - mid {
        // The left half of `a` is "moved" to `buf`.
        ptr::copy_nonoverlapping::<T>(a, buf, mid);
        let buf_end = buf.add(mid);

        let mut right = a_mid;
        let mut left = buf;
        let mut out = a;

        if is_less(&*right.add(len - mid - 1), &*left.add(mid - 1)) {
            // right ends first

            while right < a_end {
                let src_ptr = if is_less(&*right, &*left) {
                    let res = right;
                    right = right.add(1);
                    res
                } else {
                    let res = left;
                    left = left.add(1);
                    res
                };
                ptr::copy_nonoverlapping(src_ptr, out, 1);
                out = out.add(1);
            }
            ptr::copy_nonoverlapping(left, out, a_end.offset_from(out) as _);
        } else {
            // left ends first

            while left < buf_end {
                let src_ptr = if is_less(&*right, &*left) {
                    let res = right;
                    right = right.add(1);
                    res
                } else {
                    let res = left;
                    left = left.add(1);
                    res
                };
                ptr::copy_nonoverlapping(src_ptr, out, 1);
                out = out.add(1);
            }
        }
    } else {
        // The right half of `a` is "moved" to `buf`.
        ptr::copy_nonoverlapping::<T>(a_mid, buf, len - mid);
        let buf_end = buf.add(len - mid);

        let mut left = a_mid.sub(1);
        let mut right = buf_end.sub(1);
        let mut out = a_end;

        if is_less(&*right.sub(len - mid - 1), &*left.sub(mid - 1)) {
            // left ends first

            while a <= left {
                let src_ptr = if is_less(&*right, &*left) {
                    let res = left;
                    left = left.sub(1);
                    res
                } else {
                    let res = right;
                    right = right.sub(1);
                    res
                };
                out = out.sub(1);
                ptr::copy_nonoverlapping(src_ptr, out, 1);
            }
            ptr::copy_nonoverlapping(buf, a, out.offset_from(a) as _);
        } else {
            // right ends first

            while buf <= right {
                let src_ptr = if is_less(&*right, &*left) {
                    &mut left
                } else {
                    &mut right
                };
                out = out.sub(1);
                ptr::copy_nonoverlapping(*src_ptr, out, 1);
                *src_ptr = src_ptr.sub(1);
            }
        }
    }
}

/// Merges four consecutive sorted runs together.
/// This function doesn't read from `buf`, so it is safe and recomended to reuse `buf` for multiple merges.
///
/// # SAFETY
/// Don't read from `buf` since it will contain a partial shallow copy of `a` after the execution.
/// Make sure that `a[..m]` and `a[m..]` are sorted, so that nothing wierd happens.
///
/// # Panics
/// This function will panic when `mid` isn't sorted or is outside the range `0..=a.len()`.
/// Or if `buf` is not big enough to perform the merge (This won't panic if `buf.len()` is at least `a.len()`).
pub unsafe fn quad_merge<T, F: FnMut(&T, &T) -> bool>(
    a: &mut [T],
    mid: [usize; 3],
    buf: *mut T,
    is_less: &mut F,
) {
    debug_assert!(0 < mid[0]);
    debug_assert!(mid[0] < mid[1]);
    debug_assert!(mid[1] < mid[2]);
    debug_assert!(mid[2] < a.len());

    let len = a.len();
    let a = a.as_mut_ptr();
    let (mid0, mid1, mid2) = (a.add(mid[0]), a.add(mid[1]), a.add(mid[2]));
    let a_end = a.add(len);

    let (buf_mid, buf_end) = (buf.add(mid[1]), buf.add(len));

    // main: [A][B][C][D]
    // swap:
    general_merge(a, mid0, mid1, buf, is_less);
    // main:       [C][D]
    // swap: [A  B]
    general_merge(mid1, mid2, a_end, buf_mid, is_less);
    // main:
    // swap: [A  B][C  D]
    general_merge(buf, buf_mid, buf_end, a, is_less);
    // main: [A  B  C  D]
    // swap:
}

/// Merges four consecutive sorted runs together.
/// This function doesn't read from `buf`, so it is safe and recomended to reuse `buf` for multiple merges.
///
/// # SAFETY
/// Don't read from `buf` since it will contain a partial shallow copy of `a` after the execution.
/// Make sure that `a[..m]` and `a[m..]` are sorted, so that nothing wierd happens.
///
/// # Panics
/// This function will panic when `mid` isn't sorted or is outside the range `0..=a.len()`.
/// Or if `buf` is not big enough to perform the merge (This won't panic if `buf.len()` is at least `a.len()`).
pub unsafe fn tri_merge<T, F: FnMut(&T, &T) -> bool>(
    a: &mut [T],
    mid: [usize; 2],
    buf: *mut T,
    is_less: &mut F,
) {
    debug_assert!(mid[0] <= mid[1]);
    debug_assert!(mid[1] <= a.len());

    if mid[1] == 0 || mid[0] == a.len() {
        return;
    } else if mid[1] == a.len() || mid[0] == mid[1] {
        merge(a, mid[0], buf, is_less);
    } else if mid[0] == 0 {
        merge(a, mid[1], buf, is_less);
    }

    let len = a.len();
    let a = a.as_mut_ptr();
    let (mid0, mid1) = (a.add(mid[0]), a.add(mid[1]));
    let a_end = a.add(len);

    // Chooses whether to "move" the left or the right half of `a` into `buf`.
    if mid[1] <= len - mid[0] {
        // The left half of `a` is "moved" to `buf`.
        general_merge(a, mid0, mid1, buf, is_less);
        let buf_end = buf.add(mid[1]);

        let mut right = mid1;
        let mut left = buf;
        let mut out = a;

        if is_less(&*right.add(len - mid[1] - 1), &*left.add(mid[1] - 1)) {
            // right ends first

            while right < a_end {
                let src_ptr = if is_less(&*right, &*left) {
                    let res = right;
                    right = right.add(1);
                    res
                } else {
                    let res = left;
                    left = left.add(1);
                    res
                };
                ptr::copy_nonoverlapping(src_ptr, out, 1);
                out = out.add(1);
            }
            ptr::copy_nonoverlapping(left, out, a_end.offset_from(out) as _);
        } else {
            // left ends first

            while left < buf_end {
                let src_ptr = if is_less(&*right, &*left) {
                    let res = right;
                    right = right.add(1);
                    res
                } else {
                    let res = left;
                    left = left.add(1);
                    res
                };
                ptr::copy_nonoverlapping(src_ptr, out, 1);
                out = out.add(1);
            }
        }
    } else {
        // The right half of `a` is "moved" to `buf`.
        general_merge(mid0, mid1, a_end, buf, is_less);
        let buf_end = buf.add(len - mid[0]);

        let mut left = mid0.sub(1);
        let mut right = buf_end.sub(1);
        let mut out = a_end;

        if is_less(&*right.sub(len - mid[0] - 1), &*left.sub(mid[0] - 1)) {
            // left ends first

            while a <= left {
                let src_ptr = if is_less(&*right, &*left) {
                    let res = left;
                    left = left.sub(1);
                    res
                } else {
                    let res = right;
                    right = right.sub(1);
                    res
                };
                out = out.sub(1);
                ptr::copy_nonoverlapping(src_ptr, out, 1);
            }
            ptr::copy_nonoverlapping(buf, a, out.offset_from(a) as _);
        } else {
            // right ends first

            while buf <= right {
                let src_ptr = if is_less(&*right, &*left) {
                    &mut left
                } else {
                    &mut right
                };
                out = out.sub(1);
                ptr::copy_nonoverlapping(*src_ptr, out, 1);
                *src_ptr = src_ptr.sub(1);
            }
        }
    }
}

/// The classic basic merge. A classic merge sort implementation would copy from `out` back to `start` after merging.
///
/// # SAFETY
/// `out` has to have length of at least `end.offset_from(start)` allocated.
/// `start <= mid && mid <= end`
unsafe fn general_merge<T, F: FnMut(&T, &T) -> bool>(
    start: *mut T,
    mid: *mut T,
    end: *mut T,
    mut out: *mut T,
    is_less: &mut F,
) {
    if start == mid {
        ptr::copy_nonoverlapping(mid, out, end.offset_from(mid) as _);
        return;
    } else if mid == end {
        ptr::copy_nonoverlapping(start, out, mid.offset_from(start) as _);
        return;
    }

    let mut left = start;
    let mut right = mid;

    if is_less(&*end.sub(1), &*mid.sub(1)) {
        // right.last() < left.last()

        while right < end {
            let src_ptr = if is_less(&*right, &*left) {
                let res = right;
                right = right.add(1);
                res
            } else {
                let res = left;
                left = left.add(1);
                res
            };
            ptr::copy_nonoverlapping(src_ptr, out, 1);
            out = out.add(1);
        }

        ptr::copy_nonoverlapping(left, out, mid.offset_from(left) as _);
    } else {
        // left.last() <= right.last()

        while left < mid {
            let src_ptr = if is_less(&*right, &*left) {
                let res = right;
                right = right.add(1);
                res
            } else {
                let res = left;
                left = left.add(1);
                res
            };
            ptr::copy_nonoverlapping(src_ptr, out, 1);
            out = out.add(1);
        }

        ptr::copy_nonoverlapping(right, out, end.offset_from(right) as _);
    }
}

/// Cuts off the start and end of `a` with binary searching. It's more adaptive than `merge` but slower on random data than.
///
/// # SAFETY
/// See `merge`.
pub unsafe fn cutting_merge<T, F: FnMut(&T, &T) -> bool>(
    a: &mut [T],
    mid: usize,
    buf: *mut T,
    is_less: &mut F,
) {
    const MAX_LINEAR: usize = 0;

    assert!((0..=a.len()).contains(&mid));
    if mid == 0 || mid == a.len() {
        return;
    }

    let l = 'l_block: loop {
        let key = &a[mid];
        for i in 0..mid.min(MAX_LINEAR) {
            if is_less(key, a.get_unchecked(i)) {
                break 'l_block i;
            }
        }

        break binary_search_by(key, &a[..mid], &mut |a, b| !is_less(b, a));
    };
    let r = 'r_block: loop {
        let key = &a[mid - 1];
        for i in (mid.max(a.len().saturating_sub(MAX_LINEAR))..a.len()).rev() {
            if is_less(a.get_unchecked(i), key) {
                break 'r_block i + 1;
            }
        }

        break binary_search_by(key, &a[mid..], is_less) + mid;
    };

    let len = r - l;
    if len == 0 {
        return;
    }

    let a = a.as_mut_ptr().add(l);
    let mid = mid - l;
    let (a_mid, a_end) = (a.add(mid), a.add(len));

    // Chooses whether to "move" the left or the right half of `a` into `buf`.
    if mid <= len - mid {
        // The left half of `a` is "moved" to `buf`.
        ptr::copy_nonoverlapping::<T>(a, buf, mid);

        let mut right = a_mid;
        let mut left = buf;
        let mut out = a;

        while right < a_end {
            let src_ptr = if is_less(&*right, &*left) {
                let res = right;
                right = right.add(1);
                res
            } else {
                let res = left;
                left = left.add(1);
                res
            };
            ptr::copy_nonoverlapping(src_ptr, out, 1);
            out = out.add(1);
        }
        ptr::copy_nonoverlapping(left, out, a_end.offset_from(out) as _);
    } else {
        // The right half of `a` is "moved" to `buf`.
        ptr::copy_nonoverlapping::<T>(a_mid, buf, len - mid);
        let buf_end = buf.add(len - mid);

        let mut left = a_mid.sub(1);
        let mut right = buf_end.sub(1);
        let mut out = a_end;

        while a <= left {
            let src_ptr = if is_less(&*right, &*left) {
                let res = left;
                left = left.sub(1);
                res
            } else {
                let res = right;
                right = right.sub(1);
                res
            };
            out = out.sub(1);
            ptr::copy_nonoverlapping(src_ptr, out, 1);
        }
        ptr::copy_nonoverlapping(buf, a, out.offset_from(a) as _);
    }
}
