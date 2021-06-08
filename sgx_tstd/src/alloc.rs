// Licensed to the Apache Software Foundation (ASF) under one
// or more contributor license agreements.  See the NOTICE file
// distributed with this work for additional information
// regarding copyright ownership.  The ASF licenses this file
// to you under the Apache License, Version 2.0 (the
// "License"); you may not use this file except in compliance
// with the License.  You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations
// under the License..

//! Memory allocation APIs
//!
//! In a given program, the standard library has one “global” memory allocator
//! that is used for example by `Box<T>` and `Vec<T>`.
//!

use core::sync::atomic::{AtomicPtr, Ordering};
use core::{mem, ptr};
use crate::sys_common::util::dumb_print;

#[doc(inline)]
pub use alloc_crate::alloc::*;

pub use sgx_alloc::System;

static HOOK: AtomicPtr<()> = AtomicPtr::new(ptr::null_mut());

/// Registers a custom allocation error hook, replacing any that was previously registered.
///
/// The allocation error hook is invoked when an infallible memory allocation fails, before
/// the runtime aborts. The default hook prints a message to standard error,
/// but this behavior can be customized with the [`set_alloc_error_hook`] and
/// [`take_alloc_error_hook`] functions.
///
/// The hook is provided with a `Layout` struct which contains information
/// about the allocation that failed.
///
/// The allocation error hook is a global resource.
pub fn set_alloc_error_hook(hook: fn(Layout)) {
    HOOK.store(hook as *mut (), Ordering::SeqCst);
}

/// Unregisters the current allocation error hook, returning it.
///
/// *See also the function [`set_alloc_error_hook`].*
///
/// If no custom hook is registered, the default hook will be returned.
pub fn take_alloc_error_hook() -> fn(Layout) {
    let hook = HOOK.swap(ptr::null_mut(), Ordering::SeqCst);
    if hook.is_null() { default_alloc_error_hook } else { unsafe { mem::transmute(hook) } }
}

fn default_alloc_error_hook(layout: Layout) {
    dumb_print(format_args!("memory allocation of {} bytes failed", layout.size()));
}

pub use stats_alloc::alloc_stats;

mod stats_alloc {
    use core::alloc::{GlobalAlloc, Layout};
    use core::sync::atomic::{AtomicIsize, AtomicUsize, Ordering};
    use sgx_alloc::System;

    /// An instrumenting middleware which keeps track of allocation, deallocation,
    /// and reallocation requests to the underlying global allocator.
    #[derive(Default, Debug)]
    pub struct StatsAlloc<T: GlobalAlloc> {
        allocations: AtomicUsize,
        deallocations: AtomicUsize,
        reallocations: AtomicUsize,
        bytes_allocated: AtomicUsize,
        bytes_deallocated: AtomicUsize,
        bytes_reallocated: AtomicIsize,
        inner: T,
    }

    /// Allocator statistics
    #[derive(Clone, Copy, Default, Debug, Hash, PartialEq, Eq)]
    pub struct Stats {
        /// Count of allocation operations
        pub allocations: usize,
        /// Count of deallocation operations
        pub deallocations: usize,
        /// Count of reallocation operations
        ///
        /// An example where reallocation may occur: resizing of a `Vec<T>` when
        /// its length would excceed its capacity. Excessive reallocations may
        /// indicate that resizable data structures are being created with
        /// insufficient or poorly estimated initial capcities.
        ///
        /// ```
        /// let mut x = Vec::with_capacity(1);
        /// x.push(0);
        /// x.push(1); // Potential reallocation
        /// ```
        pub reallocations: usize,
        /// Total bytes requested by allocations
        pub bytes_allocated: usize,
        /// Total bytes freed by deallocations
        pub bytes_deallocated: usize,
        /// Total of bytes requested minus bytes freed by reallocations
        ///
        /// This number is positive if the total bytes requested by reallocation
        /// operations is greater than the total bytes freed by reallocations. A
        /// positive value indicates that resizable structures are growing, while
        /// a negative value indicates that such structures are shrinking.
        pub bytes_reallocated: isize,
    }

    /// An instrumented instance of the system allocator.
    pub static INSTRUMENTED_SYSTEM: StatsAlloc<System> = StatsAlloc {
        allocations: AtomicUsize::new(0),
        deallocations: AtomicUsize::new(0),
        reallocations: AtomicUsize::new(0),
        bytes_allocated: AtomicUsize::new(0),
        bytes_deallocated: AtomicUsize::new(0),
        bytes_reallocated: AtomicIsize::new(0),
        inner: System,
    };

    impl StatsAlloc<System> {
        /// Provides access to an instrumented instance of the system allocator.
        pub const fn system() -> Self {
            StatsAlloc {
                allocations: AtomicUsize::new(0),
                deallocations: AtomicUsize::new(0),
                reallocations: AtomicUsize::new(0),
                bytes_allocated: AtomicUsize::new(0),
                bytes_deallocated: AtomicUsize::new(0),
                bytes_reallocated: AtomicIsize::new(0),
                inner: System,
            }
        }
    }

    impl<T: GlobalAlloc> StatsAlloc<T> {
        /// Provides access to an instrumented instance of the given global
        /// allocator.
        #[cfg(feature = "nightly")]
        pub const fn new(inner: T) -> Self {
            StatsAlloc {
                allocations: AtomicUsize::new(0),
                deallocations: AtomicUsize::new(0),
                reallocations: AtomicUsize::new(0),
                bytes_allocated: AtomicUsize::new(0),
                bytes_deallocated: AtomicUsize::new(0),
                bytes_reallocated: AtomicIsize::new(0),
                inner,
            }
        }

        /// Provides access to an instrumented instance of the given global
        /// allocator.
        #[cfg(not(feature = "nightly"))]
        pub fn new(inner: T) -> Self {
            StatsAlloc {
                allocations: AtomicUsize::new(0),
                deallocations: AtomicUsize::new(0),
                reallocations: AtomicUsize::new(0),
                bytes_allocated: AtomicUsize::new(0),
                bytes_deallocated: AtomicUsize::new(0),
                bytes_reallocated: AtomicIsize::new(0),
                inner,
            }
        }

        /// Takes a snapshot of the current view of the allocator statistics.
        pub fn stats(&self) -> Stats {
            Stats {
                allocations: self.allocations.load(Ordering::SeqCst),
                deallocations: self.deallocations.load(Ordering::SeqCst),
                reallocations: self.reallocations.load(Ordering::SeqCst),
                bytes_allocated: self.bytes_allocated.load(Ordering::SeqCst),
                bytes_deallocated: self.bytes_deallocated.load(Ordering::SeqCst),
                bytes_reallocated: self.bytes_reallocated.load(Ordering::SeqCst),
            }
        }
    }

    unsafe impl<'a, T: GlobalAlloc + 'a> GlobalAlloc for &'a StatsAlloc<T> {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            (*self).alloc(layout)
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            (*self).dealloc(ptr, layout)
        }

        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            (*self).alloc_zeroed(layout)
        }

        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            (*self).realloc(ptr, layout, new_size)
        }
    }

    unsafe impl<T: GlobalAlloc> GlobalAlloc for StatsAlloc<T> {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            self.allocations.fetch_add(1, Ordering::SeqCst);
            self.bytes_allocated.fetch_add(layout.size(), Ordering::SeqCst);
            self.inner.alloc(layout)
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            self.deallocations.fetch_add(1, Ordering::SeqCst);
            self.bytes_deallocated.fetch_add(layout.size(), Ordering::SeqCst);
            self.inner.dealloc(ptr, layout)
        }

        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            self.allocations.fetch_add(1, Ordering::SeqCst);
            self.bytes_allocated.fetch_add(layout.size(), Ordering::SeqCst);
            self.inner.alloc_zeroed(layout)
        }

        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            self.reallocations.fetch_add(1, Ordering::SeqCst);
            if new_size > layout.size() {
                let difference = new_size - layout.size();
                self.bytes_allocated.fetch_add(difference, Ordering::SeqCst);
            } else if new_size < layout.size() {
                let difference = layout.size() - new_size;
                self.bytes_deallocated.fetch_add(difference, Ordering::SeqCst);
            }
            self.bytes_reallocated
                .fetch_add(new_size.wrapping_sub(layout.size()) as isize, Ordering::SeqCst);
            self.inner.realloc(ptr, layout, new_size)
        }
    }

    pub fn alloc_stats() -> Stats {
        INSTRUMENTED_SYSTEM.stats()
    }
}

#[global_allocator]
static ALLOC: &'static stats_alloc::StatsAlloc<sgx_alloc::System> = &stats_alloc::INSTRUMENTED_SYSTEM;

#[doc(hidden)]
#[alloc_error_handler]
pub fn rust_oom(layout: Layout) -> ! {
    let hook = HOOK.load(Ordering::SeqCst);
    let hook: fn(Layout) =
        if hook.is_null() { default_alloc_error_hook } else { unsafe { mem::transmute(hook) } };
    hook(layout);
    unsafe { crate::sys::abort_internal() }
}

#[doc(hidden)]
#[allow(unused_attributes)]
pub mod __default_lib_allocator {
    use super::{GlobalAlloc, Layout, System};
    // These magic symbol names are used as a fallback for implementing the
    // `__rust_alloc` etc symbols (see `src/liballoc/alloc.rs`) when there is
    // no `#[global_allocator]` attribute.

    // for symbol names src/librustc_ast/expand/allocator.rs
    // for signatures src/librustc_allocator/lib.rs

    // linkage directives are provided as part of the current compiler allocator
    // ABI

    #[rustc_std_internal_symbol]
    pub unsafe extern "C" fn __rdl_alloc(size: usize, align: usize) -> *mut u8 {
        let layout = Layout::from_size_align_unchecked(size, align);
        System.alloc(layout)
    }

    #[rustc_std_internal_symbol]
    pub unsafe extern "C" fn __rdl_dealloc(ptr: *mut u8, size: usize, align: usize) {
        System.dealloc(ptr, Layout::from_size_align_unchecked(size, align))
    }

    #[rustc_std_internal_symbol]
    pub unsafe extern "C" fn __rdl_realloc(
        ptr: *mut u8,
        old_size: usize,
        align: usize,
        new_size: usize,
    ) -> *mut u8 {
        let old_layout = Layout::from_size_align_unchecked(old_size, align);
        System.realloc(ptr, old_layout, new_size)
    }

    #[rustc_std_internal_symbol]
    pub unsafe extern "C" fn __rdl_alloc_zeroed(size: usize, align: usize) -> *mut u8 {
        let layout = Layout::from_size_align_unchecked(size, align);
        System.alloc_zeroed(layout)
    }
}