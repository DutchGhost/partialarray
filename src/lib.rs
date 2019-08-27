#![no_std]
#![feature(const_generics)]

use core::{mem::MaybeUninit, ops, ptr, slice};

/// This struct is a simple wrapper around `[MaybeUninit<T>; N]`.
///
/// Because of a bug in const generics, this struct has no `new` or `uninit` method.
/// Use [`Default::default()`] instead to create one.
///
/// The traits `Index` and `IndexMut` are also implemeted, so one can write an expression like:
/// ```Rust
/// array[0] = MaybeUninit::new(10)
/// ```
/// To get pointers to an element T in the array, use [`MaybeArray::nth_ptr`] and
/// [`MaybeArray::nth_ptr_mut`].
///
/// To read/write to an element, use [`MaybeArray::read`] and [`MaybeArray::write`].
///
/// Finally to transform the MaybeArray into a `[T; N]`, use [`MaybeArray::into_array`].
///
/// This struct should be used with a warning, since its a verry thin wrapper,
/// and does not provide `Drop` implementation. Any user is responsible for dropping elements.
#[repr(transparent)]
pub struct MaybeArray<T, const N: usize> {
    array: [MaybeUninit<T>; N],
}

impl<T: Copy, const N: usize> Copy for MaybeArray<T, { N }> {}

impl<T: Copy, const N: usize> Clone for MaybeArray<T, { N }> {
    fn clone(&self) -> Self {
        // Not calling [T; N]::clone, we cannot know if we are initialized enough for that.
        *self
    }
}

impl<T, const N: usize> Default for MaybeArray<T, { N }> {
    #[inline(always)]
    fn default() -> Self {
        Self {
            // We actually create a [MaybeUninit<T>; N] here using *another* MaybeUninit.
            // It is safe to assume the array is initialized, since a MaybeUninit<T> is always
            // initialized.
            array: unsafe { MaybeUninit::<_>::uninit().assume_init() },
        }
    }
}

impl<T, const N: usize> MaybeArray<T, { N }> {
    /// Returns the capacity of the array.
    ///
    /// # Examples
    /// ```
    /// use partialarray::MaybeArray;
    ///
    /// let array = MaybeArray::<i32, { 10 }>::default();
    ///
    /// assert_eq!(array.capacity(), 10);
    /// ```
    #[cfg(not(miri))]
    #[inline(always)]
    pub const fn capacity(&self) -> usize {
        N
    }

    #[cfg(miri)]
    #[inline(always)]
    /// Returns the capacity of the array.
    pub fn capacity(&self) -> usize {
        self.array.len()
    }

    /// Returns a pointer to the element at `offset`.
    /// This element *may* be uninitialized.
    ///
    /// if `N` is 0, for all values of `offset`, this function returns a dangling pointer.
    ///
    /// # Examples
    /// ```
    /// use partialarray::MaybeArray;
    ///
    /// let array = MaybeArray::<i32, { 4 }>::default();
    ///
    /// let ptr = array.nth_ptr(1);
    /// ```
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
    ///
    /// # Examples
    /// ```
    /// use partialarray::MaybeArray;
    ///
    /// let mut array = MaybeArray::<i32, { 4 }>::default();
    ///
    /// let ptr = array.nth_ptr_mut(1);
    /// ```
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
    /// If `N` is 0, the returned pointer is dangling, but aligned.
    ///
    /// # Examples
    /// ```
    /// use partialarray::MaybeArray;
    ///
    /// let array = MaybeArray::<String, { 10 }>::default();
    /// assert_eq!(array.first_ptr(), array.nth_ptr(0));
    /// ```
    #[inline(always)]
    pub const fn first_ptr(&self) -> *const T {
        // Using `array_ptr` here instead of `nth_ptr(0)`,
        // since `array_ptr` does no pointer offsets,
        // and just converts &MaybeArray<T, { N }> to `*const [T; N]`.
        // this pointer is equal to the first element.
        self.array_ptr() as *const T
    }

    /// Returns a mutable pointer to the first element of the array.
    /// This element *may* be uninitialized.
    ///
    /// If `N` is 0, the returned pointer is dangling, but aligned.
    ///
    /// # Examples
    /// ```
    /// use partialarray::MaybeArray;
    ///
    /// let mut array = MaybeArray::<String, { 10 }>::default();
    /// assert_eq!(array.first_ptr_mut(), array.nth_ptr_mut(0));
    /// ```
    #[inline(always)]
    pub fn first_ptr_mut(&mut self) -> *mut T {
        // Using `array_ptr_mut` here instead of `nth_ptr(_mut0)`,
        // since `array_ptr_mut` does no pointer offsets,
        // and just converts &mut MaybeArray<T, { N }> to `*mut [T; N]`.
        // this pointer is equal to the first element.
        self.array_ptr_mut() as *mut T
    }

    /// Returns a pointer to the whole array.
    /// There *may* be elements in the array that are uninitialized.
    ///
    /// # Examples
    /// ```
    /// use partialarray::MaybeArray;
    ///
    /// let mut array = MaybeArray::<Vec<i32>, { 3 }>::default();
    /// let ptr: *const [Vec<i32>; 3] = array.array_ptr();
    /// ```
    #[inline(always)]
    pub const fn array_ptr(&self) -> *const [T; N] {
        &self.array as *const [MaybeUninit<T>; N] as *const [T; N]
    }

    /// Returns a mutable pointer to the whole array.
    /// There *may* be elements in the array that are uninitialized.
    ///
    /// # Examples
    /// ```
    /// use partialarray::MaybeArray;
    ///
    /// let mut array = MaybeArray::<Vec<i32>, { 3 }>::default();
    /// let ptr: *mut [Vec<i32>; 3] = array.array_ptr_mut();
    /// ```
    #[inline(always)]
    pub fn array_ptr_mut(&mut self) -> *mut [T; N] {
        &mut self.array as *mut [MaybeUninit<T>; N] as *mut [T; N]
    }

    /// Reads the element at `offset`.
    /// After reading the element, it should be considered moved.
    ///
    /// This means calling `take` more than once with the same offset,
    /// without an intermediate write to the offset is invalid, unless `T` implements Copy.
    ///
    /// See also [`MaybeArray::write`].
    ///
    /// # Unsafe
    /// Marked unsafe because
    /// 1) `offset` is *NOT* boundschecked.
    /// 2) The element at `offset` may be uninitialized, thus reading it is invalid.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use partialarray::MaybeArray;
    ///
    /// let mut array = MaybeArray::<String, { 10 }>::default();
    /// // The 0th element is initialized.
    /// array[0] = MaybeUninit::new(String::from("hello"));
    ///     
    /// unsafe {
    ///     // Reading the 0th element is ok.
    ///     assert_eq!(array.read(0), "hello");
    /// }
    /// ```
    #[inline(always)]
    pub unsafe fn read(&self, offset: usize) -> T {
        ptr::read(self.nth_ptr(offset))
    }

    /// Sets the element at `offset` to `value`.
    /// Any previous element at `offset` is overwritten,
    /// and it's destructor will NOT run.
    ///
    /// # Unsafe
    /// Marked unsafe because `offset` is not boundschecked.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use partialarray::MaybeArray;
    ///
    /// let mut array = MaybeArray::<String, { 2 }>::default();
    ///
    /// for offset in 0..2 {
    ///     array[offset] = MaybeUninit::new(format!("I am number {}", offset));
    /// }
    ///     
    /// unsafe {
    ///     let array = MaybeArray::into_array(array);
    ///
    ///     assert_eq!(array, [String::from("I am number 0"), String::from("I am number 1")]);
    /// }
    #[inline(always)]
    pub unsafe fn write(&mut self, offset: usize, value: T) {
        ptr::write(self.nth_ptr_mut(offset), value)
    }

    /// Transforms `this` into an array.
    /// # Unsafe
    /// Marked unsafe because all elements within the `MaybeArray` *MUST*
    /// be initialized. If they are not, invoking this function is UB.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use partialarray::MaybeArray;
    ///
    /// let mut array = MaybeArray::<i32, { 3 }>::default();
    ///
    /// for offset in 0..array.capacity() {
    ///     array[offset] = MaybeUninit::new(offset as i32 + 1);
    /// }
    ///
    /// unsafe {
    ///     let array = MaybeArray::into_array(array);
    ///     assert_eq!(&array, &[1, 2, 3]);
    /// }
    /// ```
    pub unsafe fn into_array(mut this: MaybeArray<T, { N }>) -> [T; N] {
        // We dont have to `mem::forget(this)`,
        // since the inner array contains `MaybeUninit<T>`'s,
        // which will never invoke the destructor.
        let array_ptr = this.array_ptr_mut();
        ptr::read(array_ptr)
    }

    /// Returns a subslice without doing boundschecks.
    ///
    /// # Unsafe
    /// Marked unsafe because
    /// 1) the given range is NOT boundschecked
    /// 2) The elements contained within the returned slice may be uninitialized, which is UB.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use partialarray::MaybeArray;
    ///
    /// let mut array = MaybeArray::<usize, { 10 }>::default();
    ///     // Initialize elements 3..6.
    /// for offset in 3..6 {
    ///     array[offset] = MaybeUninit::new(offset);
    /// }
    ///     
    /// unsafe {
    ///     // This is ok, we get a slice to elements 3, 4 and 5.
    ///     assert_eq!(array.slice_index(3..6), &[3, 4, 5]);
    /// }
    /// ```
    #[inline]
    pub unsafe fn slice_index<R>(&self, r: R) -> &[T]
    where
        R: ops::RangeBounds<usize>,
    {
        let begin = match r.start_bound() {
            ops::Bound::Included(&start) => start,
            ops::Bound::Excluded(&start) => start + 1,
            ops::Bound::Unbounded => 0,
        };

        let end = match r.end_bound() {
            ops::Bound::Included(&end) => end + 1,
            ops::Bound::Excluded(&end) => end,
            ops::Bound::Unbounded => self.capacity(),
        };

        debug_assert!(begin <= end);
        debug_assert!(end <= self.capacity());

        slice::from_raw_parts(self.nth_ptr(begin), end - begin)
    }

    /// Returns a mutable subslice without doing boundschecks.
    ///
    /// # Unsafe
    /// Marked unsafe because
    /// 1) the given range is NOT boundschecked
    /// 2) The elements contained within the returned slice may be uninitialized, which is UB.
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use partialarray::MaybeArray;
    ///
    /// let mut array = MaybeArray::<usize, { 10 }>::default();
    /// // Initialize elements 3..6.
    /// for offset in 3..6 {
    ///     array[offset] = MaybeUninit::new(offset);
    /// }
    ///     
    /// unsafe {
    ///     // This is ok, we get a slice to elements 3, 4 and 5.
    ///     assert_eq!(array.slice_index_mut(3..6), &mut [3, 4, 5]);
    /// }
    /// ```
    #[inline]
    pub unsafe fn slice_index_mut<R>(&mut self, r: R) -> &mut [T]
    where
        R: ops::RangeBounds<usize>,
    {
        let begin = match r.start_bound() {
            ops::Bound::Included(&start) => start,
            ops::Bound::Excluded(&start) => start + 1,
            ops::Bound::Unbounded => 0,
        };

        let end = match r.end_bound() {
            ops::Bound::Included(&end) => end + 1,
            ops::Bound::Excluded(&end) => end,
            ops::Bound::Unbounded => self.capacity(),
        };

        debug_assert!(begin <= end);
        debug_assert!(end <= self.capacity());

        slice::from_raw_parts_mut(self.nth_ptr_mut(begin), end - begin)
    }
}

impl<T, const N: usize> ops::Index<usize> for MaybeArray<T, { N }> {
    type Output = MaybeUninit<T>;

    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        &self.array[index]
    }
}

impl<T, const N: usize> ops::IndexMut<usize> for MaybeArray<T, { N }> {
    #[inline(always)]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.array[index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::MaybeUninit;
    
    #[test]
    fn maybearray() {
        let mut array = MaybeArray::<i32, { 10 }>::default();

        array[0] = MaybeUninit::new(10);

        unsafe { assert_eq!(*(array.first_ptr()), 10) }
    }

    #[test]
    fn test_zero_len() {
        let mut array = MaybeArray::<i32, { 0 }>::default();

        let ptr = array.first_ptr();
        assert!(ptr as usize % core::mem::align_of::<i32>() == 0);
    }

    #[test]
    fn test_slice_index() {
        let mut array = MaybeArray::<i32, { 4 }>::default();

        for idx in 0..4 {
            array[idx] = MaybeUninit::new((idx as i32 + 1) * 2);
        }

        unsafe {
            let slice = array.slice_index(2..);
            assert_eq!(slice, &[6, 8][..]);

            let slice = array.slice_index(0..=1);
            assert_eq!(slice, &[2, 4]);

            let slice = array.slice_index(1..3);
            assert_eq!(slice, &[4, 6]);
        }
    }

    #[test]
    fn test_read() {
        let mut array = MaybeArray::<String, { 10 }>::default();
        // The 0th element is initialized.
        array[0] = MaybeUninit::new(String::from("hello"));
        
        unsafe {
            // Reading the 0th element is ok.
            assert_eq!(array.read(0), "hello");
        }
    }

}
