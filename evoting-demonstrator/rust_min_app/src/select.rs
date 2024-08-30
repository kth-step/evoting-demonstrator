extern crate libc;

/// References
/// https://blog.pjam.me/posts/select-syscall-in-rust/
/// https://github.com/nix-rust/nix/blob/master/src/sys/select.rs
/// https://github.com/rust-lang/libc/blob/master/src/unix/bsd/mod.rs
use std::{
  os::unix::io::RawFd,
  {io, mem, ptr, time},
};

/// FdSet is a wrapper for libc::fd_set
/// fd_set is platform dependently defined within
/// https://github.com/rust-lang/libc/blob/master/src/unix/bsd/mod.rs
/// ```c
/// pub struct fd_set {
///     #[cfg(all(target_pointer_width = "64",
///             any(target_os = "freebsd", target_os = "dragonfly")))]
///     fds_bits: [i64; FD_SETSIZE / 64],
///     #[cfg(not(all(target_pointer_width = "64",
///                 any(target_os = "freebsd", target_os = "dragonfly"))))]
///     fds_bits: [i32; FD_SETSIZE / 32],
/// }
/// ```
///
pub struct FdSet(libc::fd_set);

/// FdSet implementation makes use of the libc macros:
/// `FD_ZERO`, `FD_CLR`, `FD_SET`, `FD_ISSET`
impl FdSet {
  pub fn new() -> FdSet {
    unsafe {
      // MaybeUninit<libc::fd_set> for “out-pointers”: return a pointer
      // to some (uninitialized) memory
      // https://doc.rust-lang.org/stable/std/mem/union.MaybeUninit.html#out-pointers
      let mut raw_fd_set = mem::MaybeUninit::<libc::fd_set>::uninit();
      // clears allocated memory
      libc::FD_ZERO(raw_fd_set.as_mut_ptr());
      FdSet(raw_fd_set.assume_init())
    }
  }
  pub fn clear(&mut self, fd: RawFd) {
    unsafe { libc::FD_CLR(fd, &mut self.0) }
  }
  pub fn set(&mut self, fd: RawFd) {
    unsafe { libc::FD_SET(fd, &mut self.0) }
  }
  pub fn is_set(&mut self, fd: RawFd) -> bool {
    unsafe { libc::FD_ISSET(fd, &self.0) }
  }
}

impl Default for FdSet {
  fn default() -> Self {
    Self::new()
  }
}

/// convert between Rust option and C pointers
fn to_fdset_ptr(opt: Option<&mut FdSet>) -> *mut libc::fd_set {
  match opt {
    None => ptr::null_mut(),
    Some(&mut FdSet(ref mut raw_fd_set)) => raw_fd_set,
  }
}
fn to_ptr<T>(opt: Option<&T>) -> *const T {
  match opt {
    None => ptr::null::<T>(),
    Some(p) => p,
  }
}

/// creates a timeval as expected by select
#[cfg(target_arch = "x86_64")]
fn make_timeval(duration: time::Duration) -> libc::timeval {
  libc::timeval {
    tv_sec: duration.as_secs() as i64,
    tv_usec: duration.subsec_micros() as i64,
  }
}

#[cfg(target_arch = "arm")]
fn make_timeval(duration: time::Duration) -> libc::timeval {
  libc::timeval {
    tv_sec: duration.as_secs() as i32,
    tv_usec: duration.subsec_micros() as i32,
  }
}

/// binding to `libc::select`
pub fn select(
  nfds: libc::c_int,
  readfds: Option<&mut FdSet>,
  writefds: Option<&mut FdSet>,
  errorfds: Option<&mut FdSet>,
  timeout: Option<time::Duration>,
) -> io::Result<usize> {
  let timeout = timeout.map(make_timeval);
  match unsafe {
    libc::select(
      nfds,
      to_fdset_ptr(readfds),
      to_fdset_ptr(writefds),
      to_fdset_ptr(errorfds),
      to_ptr::<libc::timeval>(timeout.as_ref()) as *mut libc::timeval,
    )
  } {
    -1 => Err(io::Error::last_os_error()),
    res => Ok(res as usize),
  }
}

#[cfg(target_arch = "x86_64")]
pub fn make_timespec(duration: time::Duration) -> libc::timespec {
  libc::timespec {
    tv_sec: duration.as_secs() as i64,
    tv_nsec: duration.subsec_nanos() as i64,
  }
}

#[cfg(target_arch = "arm")]
pub fn make_timespec(duration: time::Duration) -> libc::timespec {
  libc::timespec {
    tv_sec: duration.as_secs() as i32,
    tv_nsec: duration.subsec_nanos() as i32,
  }
}

/// binding to `libc::pselect`
/// mask for better control over signal handling
pub fn pselect(
  nfds: libc::c_int,
  readfds: Option<&mut FdSet>,
  writefds: Option<&mut FdSet>,
  errorfds: Option<&mut FdSet>,
  timeout: Option<time::Duration>,
  //timeout: Option<&libc::timespec>,
  sigmask: Option<&libc::sigset_t>,
) -> io::Result<usize> {
  let timeout = timeout.map(make_timespec);
  match unsafe {
    libc::pselect(
      nfds,
      to_fdset_ptr(readfds),
      to_fdset_ptr(writefds),
      to_fdset_ptr(errorfds),
      to_ptr::<libc::timespec>(timeout.as_ref()) as *mut libc::timespec,
      //to_ptr(timeout),
      to_ptr(sigmask),
    )
  } {
    -1 => Err(io::Error::last_os_error()),
    res => Ok(res as usize),
  }
}
