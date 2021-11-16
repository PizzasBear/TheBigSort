use std::{mem, ptr};

/// # SAFETY
/// This function assumes that the length of `a` is 4. It doesn't check for performance
/// reasons.
pub unsafe fn sort4<T, F: FnMut(&T, &T) -> bool>(a: *mut T, is_less: &mut F) {
    let mut swap: [T; 4] = mem::MaybeUninit::uninit().assume_init();

    if is_less(&*a.add(1), &*a) {
        ptr::copy_nonoverlapping(a.add(1), &mut swap[0], 1);
        ptr::copy_nonoverlapping(a, &mut swap[1], 1);
    } else {
        ptr::copy_nonoverlapping(a, &mut swap[0], 1);
        ptr::copy_nonoverlapping(a.add(1), &mut swap[1], 1);
    }

    if is_less(&*a.add(3), &*a.add(2)) {
        ptr::copy_nonoverlapping(a.add(3), &mut swap[2], 1);
        ptr::copy_nonoverlapping(a.add(2), &mut swap[3], 1);
    } else {
        ptr::copy_nonoverlapping(a.add(2), &mut swap[2], 1);
        ptr::copy_nonoverlapping(a.add(3), &mut swap[3], 1);
    }

    if !is_less(&swap[2], &swap[1]) {
        ptr::copy_nonoverlapping(&swap[0], a, 1);
        ptr::copy_nonoverlapping(&swap[1], a.add(1), 1);
        ptr::copy_nonoverlapping(&swap[2], a.add(2), 1);
        ptr::copy_nonoverlapping(&swap[3], a.add(3), 1);
    } else if is_less(&swap[3], &swap[0]) {
        ptr::copy_nonoverlapping(&swap[2], a, 1);
        ptr::copy_nonoverlapping(&swap[3], a.add(1), 1);
        ptr::copy_nonoverlapping(&swap[0], a.add(2), 1);
        ptr::copy_nonoverlapping(&swap[1], a.add(3), 1);
    } else {
        if !is_less(&swap[2], &swap[0]) {
            ptr::copy_nonoverlapping(&swap[0], a, 1);
            ptr::copy_nonoverlapping(&swap[2], a.add(1), 1);
        } else {
            ptr::copy_nonoverlapping(&swap[2], a, 1);
            ptr::copy_nonoverlapping(&swap[0], a.add(1), 1);
        }

        if !is_less(&swap[3], &swap[1]) {
            ptr::copy_nonoverlapping(&swap[1], a.add(2), 1);
            ptr::copy_nonoverlapping(&swap[3], a.add(3), 1);
        } else {
            ptr::copy_nonoverlapping(&swap[3], a.add(2), 1);
            ptr::copy_nonoverlapping(&swap[1], a.add(3), 1);
        }
    }
}
/// # SAFETY
/// This function assumes that the length of `a` is 3. It doesn't check for performance
/// reasons.
pub unsafe fn sort3<T, F: FnMut(&T, &T) -> bool>(a: *mut T, is_less: &mut F) {
    let mut swap = mem::MaybeUninit::uninit().assume_init();

    if is_less(&*a.add(1), &*a) {
        if !is_less(&*a.add(2), &*a) {
            ptr::copy_nonoverlapping(a, &mut swap, 1);
            ptr::copy_nonoverlapping(a.add(1), a, 1);
            ptr::copy_nonoverlapping(&swap, a.add(1), 1);
        } else if is_less(&*a.add(2), &*a.add(1)) {
            ptr::copy_nonoverlapping(a, &mut swap, 1);
            ptr::copy_nonoverlapping(a.add(2), a, 1);
            ptr::copy_nonoverlapping(&swap, a.add(2), 1);
        } else {
            ptr::copy_nonoverlapping(a, &mut swap, 1);
            ptr::copy_nonoverlapping(a.add(1), a, 1);
            ptr::copy_nonoverlapping(a.add(2), a.add(1), 1);
            ptr::copy_nonoverlapping(&swap, a.add(2), 1);
        }
    } else if is_less(&*a.add(2), &*a.add(1)) {
        if is_less(&*a.add(2), &*a) {
            ptr::copy_nonoverlapping(a.add(2), &mut swap, 1);
            ptr::copy_nonoverlapping(a.add(1), a.add(2), 1);
            ptr::copy_nonoverlapping(a, a.add(1), 1);
            ptr::copy_nonoverlapping(&swap, a, 1);
        } else {
            ptr::copy_nonoverlapping(a.add(2), &mut swap, 1);
            ptr::copy_nonoverlapping(a.add(1), a.add(2), 1);
            ptr::copy_nonoverlapping(&swap, a.add(1), 1);
        }
    }
}

/// # SAFETY
/// This function assumes that the length of `a` is 2. It doesn't check for performance
/// reasons.
pub unsafe fn sort2<T, F: FnMut(&T, &T) -> bool>(a: *mut T, is_less: &mut F) {
    let mut swap = mem::MaybeUninit::uninit().assume_init();

    if is_less(&*a.add(1), &*a) {
        ptr::copy_nonoverlapping(a, &mut swap, 1);
        ptr::copy_nonoverlapping(a.add(1), a, 1);
        ptr::copy_nonoverlapping(&swap, a.add(1), 1);
    }
}
