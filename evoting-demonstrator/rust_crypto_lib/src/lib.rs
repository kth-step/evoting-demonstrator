#![allow(clippy::not_unsafe_ptr_arg_deref,unused_variables)]


#![no_std]
// extern crate libc;

use core::ffi::{c_long,c_uchar};
use hacspec_lib::{Vec,vec};

#[cfg(debug_assertions)]
macro_rules! log {
    ($( $args:expr ),*) => {
        eprintln!( $( $args ),* )
    }
}

#[cfg(not(debug_assertions))]
macro_rules! log {
    ($( $args:expr ),*) => {
        ()
    };
}

pub mod crypto;

// write a number to a vector at offset, offset+1
#[allow(dead_code)]
fn int_to_byte2_offset(
    num    : i16,
    buf    : &mut Vec<u8>,
    offset : usize,
    ) {
    assert!(offset + 1 < buf.len());
    let bytes = num.to_be_bytes();
    buf[offset] = bytes[0];
    buf[offset + 1] = bytes[1];
}

// read a number from a vector at offset, offset+1
fn byte2_to_int_offset(
    buf    : &[u8],
    offset : usize,
    ) -> i16 {
    assert!(offset + 1 < buf.len());
    let bytes = [buf[offset], buf[offset + 1]];
    i16::from_be_bytes(bytes)
}

/*
/// Calls
/// ```rs
/// pub fn verify_rs256(
/// //    &public_key_pem : &[u8],
///     &signature      : &[u8],
///     &content        : &[u8],
/// ) -> Result<bool,Error>{
/// ```
/// input: `buf = sign_len:w2 pay_len:w2 sign payload`
/// output: `buf = errorcode:w ...`

#[no_mangle]
pub extern "C" fn crypto_verify_rs256(
    buf: *const c_uchar,
    len: *mut usize,
) -> *mut c_void {
    assert!(!len.is_null());
    let buf: &[u8] = unsafe {
        assert!(!buf.is_null());
        core::slice::from_raw_parts(buf, *len)
    };
    let header_len = 4;
    // read buffer length from header
    assert!(header_len <= buf.len());
    let sign_len = byte2_to_int_offset(buf, 0) as usize;
    let payload_len = byte2_to_int_offset(buf, 2) as usize;
    log!("[rs crypto_verify_rs256] header {}, sign_len {:?}, payload_len {:?}, buf.len {:?}", header_len, sign_len, payload_len, buf.len());
    assert!(header_len + sign_len + payload_len <= buf.len());
    unsafe {
        *len = 1;
    }
    let buf_vec = buf.to_vec();
    let sign = &buf_vec[header_len ..(header_len + sign_len)];
    let payload = &buf_vec[(header_len + sign_len)..(header_len + sign_len + payload_len)];
    log!("[rs crypto_verify_rs256] payload len {} sign len {}", payload.len(), sign.len());
    let bufvec = vec![crypto::verify_rs256(sign, payload) as u8];
    slice_to_malloc_buf(&bufvec)
}
*/

/*
/// Calls
/// ```rs
/// pub fn sha256(bytes: &[u8]) -> [u8; 32]
/// ```
/// input: `buf : u8`
/// output: `buf : [u8; 32]`

#[no_mangle]
pub extern "C" fn crypto_sha256(
    buf: *const c_uchar,
    len: *mut usize,
) -> *mut c_void {
    assert!(!len.is_null());
    let buf: &[u8] = unsafe {
        assert!(!buf.is_null());
        core::slice::from_raw_parts(buf, *len)
    };
    // read buffer length from header
    assert!(32 <= buf.len());
    let buflen = byte2_to_int_offset(buf, 0) as usize;
    let buf_vec = buf.to_vec();
    let buf = &buf_vec[2..(buflen+2)];
    log!("[rs crypto_sha256] buf.len {:?}, buf start {:?}", buflen, &buf_vec[0..10]);
    // log!("[rs crypto_sha256] buf end {:?}", &buf_vec[(buflen-10)..buflen]);
    let hash = crypto::sha256(buf);
    log!("[rs crypto_sha256] hash (in hex) {:x?}", &hash);
    unsafe {
        *len = 32;
    }
    slice_to_malloc_buf(&hash)
}
*/

#[allow(dead_code)]
unsafe fn buf_to_slice(buf : *const c_uchar, buf_len : *const c_long) -> &'static [u8] {
    assert!(!buf_len.is_null());
    assert!(!buf.is_null());
    core::slice::from_raw_parts(buf, buf_len as usize)
}

unsafe fn buf_to_slice_mut(buf : *mut c_uchar, buf_len : *mut c_long) -> &'static mut [u8] {
    assert!(!buf_len.is_null());
    assert!(!buf.is_null());
    core::slice::from_raw_parts_mut(buf, buf_len as usize)
}

/// Calls
/// ```rs
/// pub fn verify_rs256(
/// //    &public_key_pem : &[u8],
///     &signature      : &[u8],
///     &content        : &[u8],
/// ) -> Result<bool,Error>{
/// ```
/// input: `buf = sign_len:w2 pay_len:w2 sign payload`
/// output: `buf = errorcode:w ...`

#[no_mangle]
pub extern "C" fn fficrypto_verify_rs256(
    c : *const c_uchar,
    clen: *const c_long,
    a : *mut c_uchar,
    alen: *mut c_long,
) -> () {

    let buf = unsafe {buf_to_slice_mut(a, alen)};
    let header_len = 4;
    // read buffer length from header
    assert!(header_len <= buf.len());
    let sign_len = byte2_to_int_offset(buf, 0) as usize;
    let payload_len = byte2_to_int_offset(buf, 2) as usize;
    log!("[rs fficrypto_verify_rs256] header {}, sign_len {:?}, payload_len {:?}, buf.len {:?}", header_len, sign_len, payload_len, buf.len());
    assert!(header_len + sign_len + payload_len <= buf.len());
    let buf_vec = buf.to_vec();
    let sign = &buf_vec[header_len ..(header_len + sign_len)];
    let payload = &buf_vec[(header_len + sign_len)..(header_len + sign_len + payload_len)];
    let result = crypto::verify_rs256(sign, payload) as u8;
    log!("[rs fficrypto_verify_rs256] result {:x}", result);
    log!("[rs fficrypto_verify_rs256] payload len {} sign len {}", payload.len(), sign.len());
    buf[..1].copy_from_slice(&vec![result])
}

/// Calls
/// ```rs
/// pub fn sha256(bytes: &[u8]) -> [u8; 32]
/// ```
/// input: `buf : u8`
/// output: `buf : [u8; 32]`

#[no_mangle]
pub extern "C" fn fficrypto_sha256(
    c : *const c_uchar,
    clen: *const c_long,
    a : *mut c_uchar,
    alen: *mut c_long,
) -> () {
  let a_buf = unsafe {buf_to_slice_mut(a, alen)};

  assert!(32 <= a_buf.len());
  let buflen = byte2_to_int_offset(a_buf, 0) as usize;
  let buf_vec = a_buf.to_vec();
  let buf = &buf_vec[2..(buflen+2)];
  log!("[rs crypto_sha256] buf.len {:?}, buf start {:?}", buflen, &buf_vec[0..10]);
  // log!("[rs crypto_sha256] buf end {:?}", &buf_vec[(buflen-10)..buflen]);
  let hash = crypto::sha256(buf);
  log!("[rs crypto_sha256] hash (in hex) {:x?}", &hash);
  a_buf[..32].copy_from_slice(&hash)
}


#[cfg(test)]
mod tests {
    // importing names from outer scope
    use super::*;

    #[test]
    fn test_byte2_to_int_offset() {
        let buf: &[u8] = &vec![1, 2];
        assert_eq!(258, byte2_to_int_offset(buf, 0));
    }

    #[test]
    fn test_byte2_to_int_offset2() {
        let buf: &[u8] = &vec![1, 2, 3, 4];
        assert_eq!(772, byte2_to_int_offset(buf, 2));
    }

    #[test]
    fn test_int_to_byte2_offset() {
        let mut buf: Vec<u8> = vec![0, 0];
        int_to_byte2_offset(258, &mut buf, 0);
        assert_eq!(vec![1 as u8, 2], buf);
    }

    #[test]
    fn test_int_to_byte2_offset2() {
        let mut buf: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
        int_to_byte2_offset(300, &mut buf, 3);
        assert_eq!(vec![1, 2, 3, 1, 44, 6], buf);
    }
} // mod test
