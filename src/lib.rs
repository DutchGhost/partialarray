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
    #[cfg(not(miri))]
    #[inline(always)]
    pub const fn capacity(&self) -> usize {
        N
    }

    #[cfg(miri)]
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        self.array.len()
    }

    /// Returns a pointer to the element at `offset`.
    /// This element *may* be uninitialized.
    /// 
    /// if `N` is 0, for all values of `offset`, this function returns a dangling pointer.
    #[inline(always)]
    pub fn nth_ptr(&self, offset: usize) -> *const T {
        debug_assert!(offset <= self.capacity());

        // Can't use `add` here, since that requires the starting and resulting pointer to be in bounds,
        // or one byte past the end of the same allocated object.
        //
        // We dont know the value of `offset`, so the resulting pointer might be OOB.
        self.array.as_ptr().wrapping_add(offset) as *const T
    }

    /// Returns a mutable pointer to the element at `offset`.
    /// This element *may* be uninitialized.
    /// 
    /// if `N` is 0, for all values of `offset`, this function returns a dangling pointer.
    #[inline(always)]
    pub fn nth_ptr_mut(&mut self, offset: usize) -> *mut T {
        debug_assert!(offset <= self.capacity());

        // Can't use `add` here, since that requires the starting and resulting pointer to be in bounds,
        // or one byte past the end of the same allocated object.
        //
        // We dont know the value of `offset`, so the resulting pointer might be OOB. debug_assert!(offset <= N);
        self.array.as_mut_ptr().wrapping_add(offset) as *mut T
    }

    /// Returns a pointer to the first element of the array.
    /// This element *may* be uninitialized.
    /// 
    /// If `N` is 0, the returned pointer is dangling.
    #[inline(always)]
    pub fn first_ptr(&self) -> *const T {
        self.nth_ptr(0)
    }

    /// Returns a mutable pointer to the first element of the array.
    /// This element *may* be uninitialized.
    /// 
    /// If `N` is 0, the returned pointer is dangling.
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
    pub unsafe fn read(&mut self, offset: usize) -> T {
        ptr::read(self.nth_ptr_mut(offset))
    }

    /// Sets the element at `index` to `value`.
    /// Any previous element at `index` is overwritten,
    /// and it's destructor will NOT run.
    ///
    /// # Unsafe
    /// Marked unsafe because `index` is not boundchecked.
    #[inline(always)]
    pub unsafe fn write(&mut self, offset: usize, value: T) {
        ptr::write(self.nth_ptr_mut(offset), value)
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

    #[test]
    fn maybearray() {
        let mut array = MaybeArray::<i32, { 10 }>::default();

        unsafe {
            array.write(0, 10);
            assert_eq!(*(array.first_ptr()), 10)
        }
    }

    fn test_zero_len() {
        let mut array = MaybeArray::<i32, { 0 }>::default();

        let ptr = array.first_ptr();
    }
}
