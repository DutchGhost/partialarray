#![no_std]
#![feature(const_generics)]

use core::{mem::MaybeUninit, ptr};

/// This struct is a simple wrapper around `[MaybeUninit<T>; N]`.
///
/// To get pointers to an element T in the array, use [`MaybeArray::nth_ptr`] and
/// [`MaybeArray::nth_ptr_mut`].
///
/// To read/write to an element, use [`MaybeArray::take`] and [`MaybeArray::set`].
///
/// Finally to transforms the MaybeArray into a `[T; N]`, use [`MaybeArray::into_array`]..
///
/// This struct should be used with a warning, since its a verry thin wrapper,
/// and does not provide `Drop` implementation. Any user is responsible for dropping elements.
pub struct MaybeArray<T, const N: usize> {
    array: [MaybeUninit<T>; N],
}

impl<T, const N: usize> Default for MaybeArray<T, { N }> {
    #[inline(always)]
    fn default() -> Self {
        Self {
            array: unsafe { MaybeUninit::<_>::uninit().assume_init() },
        }
    }
}

impl<T, const N: usize> MaybeArray<T, { N }> {
    /// Returns the capacity of the array.
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Creates a MaybeArray from a normal array.
    pub fn from_array<const LEN: usize>(mut array: [T; LEN]) -> Self {
        debug_assert!(LEN > 0);
        let count = if LEN > N { N } else { LEN };

        let mut this = Self::default();

        unsafe {
            ptr::copy_nonoverlapping(&mut array[0], this.first_ptr_mut(), count);
        }

        this
    }

    /// Returns a pointer to the element at `index`.
    /// This element *may* be uninitialized.
    #[inline(always)]
    pub fn nth_ptr(&self, index: usize) -> *const T {
        debug_assert!(index < N);

        unsafe {
            let nth_element = &*(self.array.get_unchecked(index));
            nth_element.as_ptr()
        }
    }

    /// Returns a mutable pointer to the element at `index`.
    /// This element *may* be uninitialized.
    #[inline(always)]
    pub fn nth_ptr_mut(&mut self, index: usize) -> *mut T {
        debug_assert!(index < N);

        unsafe {
            let nth_element = &mut *(self.array.get_unchecked_mut(index));
            nth_element.as_mut_ptr()
        }
    }

    /// Returns a pointer to the first element of the array.
    /// This element *may* be uninitialized.
    #[inline(always)]
    pub fn first_ptr(&mut self) -> *const T {
        self.nth_ptr(0)
    }

    /// Returns a mutable pointer to the first element of the array.
    /// This element *may* be uninitialized.
    #[inline(always)]
    pub fn first_ptr_mut(&mut self) -> *mut T {
        self.nth_ptr_mut(0)
    }

    /// Returns a pointer to the whole array.
    /// There *may* be elements in the array that are uninitialized.
    #[inline(always)]
    pub const fn array_ptr(&self) -> *const [T; N] {
        &self.array as *const [MaybeUninit<T>; N] as *const [T; N]
    }

    /// Returns a mutable pointer to the whole array.
    /// There *may* be elements in the array that are uninitialized.
    #[inline(always)]
    pub fn array_ptr_mut(&mut self) -> *mut [T; N] {
        &mut self.array as *mut [MaybeUninit<T>; N] as *mut [T; N]
    }

    /// Reads the element at `index`.
    /// After reading the element, it should be considered moved.
    /// This means calling `take` more than once with the same index,
    /// without an intermediate write to the index is invalid, unless T implements Copy.
    ///
    /// # Unsafe
    /// Marked unsafe because
    /// 1) `index` is *NOT* boundschecked.
    /// 2) The element at `index` may be uninitialized, thus reading it is invalid.
    #[inline(always)]
    pub unsafe fn take(&mut self, index: usize) -> T {
        ptr::read(self.nth_ptr_mut(index))
    }

    /// Sets the element at `index` to `value`.
    /// Any previous element at `index` is overwritten,
    /// and it's destructor will NOT run.
    ///
    /// # Unsafe
    /// Marked unsafe because `index` is not boundchecked.
    #[inline(always)]
    pub unsafe fn set(&mut self, index: usize, value: T) {
        ptr::write(self.nth_ptr_mut(index), value)
    }

    /// Transforms `this` into an array.
    /// # Unsafe
    /// Marked unsafe because all elements within the `MaybeArray` *MUST*
    /// be initialized. If they are not, invoking this function is UB.
    pub unsafe fn into_array(mut this: MaybeArray<T, { N }>) -> [T; N] {
        // We dont have to `mem::forget(this)`,
        // since the inner array contains `MaybeUninit<T>`'s,
        // which will never invoke the destructor.
        let array_ptr = this.array_ptr_mut();
        ptr::read(array_ptr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // TODO: This currently fails because it expects `3usize` but finds `3usize`.
    // Expected type `[i32; _]`
    //    Found type `[i32; 3]`
    #[test]
    fn maybearray_from_array() {
        let array = MaybeArray::<i32, { 10 }>::from_array::<3usize>([1, 2, 3]);
    }
}
