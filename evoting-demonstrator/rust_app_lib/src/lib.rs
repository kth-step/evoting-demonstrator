#![allow(clippy::not_unsafe_ptr_arg_deref,unused_variables)]

extern crate libc;

#[cfg(not(feature = "emulation"))]
use crate::deserialise::Netsys_name;
#[cfg(not(feature = "emulation"))]
use core::net::{IpAddr, Ipv4Addr};

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

pub mod select;
pub mod socket;
pub mod deserialise;
pub mod config;

use crate::socket::Kind;
use crate::socket::Receive::{MarkShutdown, Message, NewClient, UDPMessage};
use crate::config::Config;
use deser_lib::{Serialise};

use std::os::unix::io::RawFd;
use std::net::SocketAddr;

use std::collections::HashMap;

// write a number to a vector at offset, offset+1
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

pub struct ASocket {
    pub hmap : HashMap<RawFd,Kind>,
    pub config : Config,
    pub queue : Vec<RawFd>,
    pub fd_net : RawFd,
    pub fd_input : Option<RawFd>,
    pub closed_fds: Vec<RawFd>,  // fds whose sender has shut down
    pub input_fds: Vec<RawFd>,   // connections established over fd_input
}

impl ASocket {
    pub fn new() -> ASocket {
      #[cfg(feature = "emulation")]
      let config = config::parse();
      #[cfg(not(feature = "emulation"))]
      let config = Config {
        id: Netsys_name::Name_VCS,
        nodes: vec![
          (Netsys_name::Name_VCS,   IpAddr::V4(Ipv4Addr::new(127,0,0,1)),8080),
          (Netsys_name::Name_Admin, IpAddr::V4(Ipv4Addr::new(192,100,1,1)),8081),
          (Netsys_name::Name_MixNet,IpAddr::V4(Ipv4Addr::new(192,100,1,1)),8082),
          (Netsys_name::Name_Client,IpAddr::V4(Ipv4Addr::new(192,100,1,1)),8083)
        ],
        socket: None,
        verbose: 3,
      };

      let mut hmap = std::collections::HashMap::new();
      let mut fd_input = None;
      let closed_fds = vec![];
      let input_fds = vec![];
      let fd_net;
      if let Some(socket_path) = &config.socket {
        fd_input = socket::socket_create(&mut hmap, socket_path).ok();
        if fd_input.is_none() {
          panic!("error creating socket at path {}", socket_path.display());
        }
      }
      if let Some(n) = config.nodes.iter().position(|(n, _, _)| *n == config.id) {
        let (_,ip,port) = config.nodes[n];
        let ip_port = format!("{ip}:{port}"); // TODO change socket_create_udp argument to ToSocketAddrs = (IpAddr, u16)
        fd_net = socket::socket_create_udp(&mut hmap, ip_port.clone()).expect("error creating udp");
        println!("UDP socket created for {ip_port} at {fd_net}");
      } else {
        // TODO should be part of config parsing
        println!("rs nodes: {:?}", config.nodes);
        println!("rs id: {:?}", config.id);
        panic!("Cannot find name {} in nodes.", config.id.to_string());
      }
      ASocket {
        hmap,
        config,
        queue: vec![],
        closed_fds,
        input_fds,
        fd_input,
        fd_net,
      }
    }
}

impl Default for ASocket {
    fn default() -> Self {
        Self::new()
    }
}

#[no_mangle]
pub extern "C" fn asocket_new() -> *mut ASocket {
    // place new object onto heap
    Box::into_raw(Box::new(ASocket::new()))
}

#[no_mangle]
pub extern "C" fn asocket_free(ptr: *mut ASocket) {
    unsafe {
        assert!(!ptr.is_null());
        let _ = Box::from_raw(ptr);
    }
}

/// ```rs
/// pub fn socket_create_udp (
///     fd_map : &mut std::collections::HashMap<RawFd,Kind>,
///     name   : &str,
/// ) -> Result<RawFd,String> {
/// ```
/// input: buf = len:w2 name:u8
/// output: buf = errorcode:w2  fd:w2 *)

#[no_mangle]
pub extern "C" fn asocket_create_udp(
    ptr: *mut ASocket,
    buf: *const libc::c_uchar,
    len: *mut usize,
) -> *mut libc::c_void {
    let asocket = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };
    assert!(!len.is_null());
    unsafe {
        assert!(4 <= *len);
    }
    let buf: &[u8] = unsafe {
        assert!(!buf.is_null());
        core::slice::from_raw_parts(buf, *len)
    };
    let str_len = byte2_to_int_offset(buf, 0) as usize;
    let name = String::from_utf8(buf[2..str_len].to_vec()).unwrap();
    log!("[rs asocket_create_udp] {:x?}", &name);
    match socket::socket_create_udp(&mut asocket.hmap, name) {
        Err(_) => {
            unsafe {
                *len = 2;
            }
            let mut buf_ret: Vec<u8> = vec![0, 0];
            int_to_byte2_offset(-1, &mut buf_ret, 0);
            slice_to_malloc_buf(&buf_ret)
        }
        Ok(fd) => {
            unsafe {
                *len = 4;
            }
            let mut bufvec = vec![0, 0, 0, 0];
            int_to_byte2_offset(0, &mut bufvec, 0);
            int_to_byte2_offset(fd as i16, &mut bufvec, 2);
            slice_to_malloc_buf(&bufvec)
        }
    }
}

/// ```rs
/// pub fn socket_create (
///     fd_map : &mut std::collections::HashMap<RawFd,Kind>,
///     name   : u32,
/// ) -> Result<RawFd,String> {
/// ```
/// input: buf = len:w2 name:u8
/// output: buf = errorcode:w2  fd:w2 *)

#[no_mangle]
pub extern "C" fn asocket_create(
    ptr: *mut ASocket,
    buf: *const libc::c_uchar,
    len: *mut usize,
) -> *mut libc::c_void {
    let asocket = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };
    assert!(!len.is_null());
    unsafe {
        assert!(4 <= *len);
    }
    let buf: &[u8] = unsafe {
        assert!(!buf.is_null());
        core::slice::from_raw_parts(buf, *len)
    };
    let str_len = byte2_to_int_offset(buf, 0) as usize;
    let name = String::from_utf8(buf[2..str_len].to_vec()).unwrap();
    log!("[rs asocket_create] {:x?}", &name);
    match socket::socket_create(&mut asocket.hmap, &name.into()) {
        Err(_) => {
            unsafe {
                *len = 2;
            }
            let mut buf_ret: Vec<u8> = vec![0, 0];
            int_to_byte2_offset(-1, &mut buf_ret, 0);
            slice_to_malloc_buf(&buf_ret)
        }
        Ok(fd) => {
            unsafe {
                *len = 4;
            }
            let mut bufvec = vec![0, 0, 0, 0];
            int_to_byte2_offset(0, &mut bufvec, 0);
            int_to_byte2_offset(fd as i16, &mut bufvec, 2);
            slice_to_malloc_buf(&bufvec)
        }
    }
}

/// Calls
/// ```rs
/// pub fn socket_receive (
///     fd_map : &mut std::collections::HashMap<RawFd,Kind>,
///     fd : RawFd,
/// ) -> Result<([u8; MAXMSGSIZE],usize),String>
/// ```
/// input: buf = fd:w2
/// output: buf = code:w2 len:w2 msg:word8array

#[no_mangle]
pub extern "C" fn asocket_receive(
    ptr: *mut ASocket,
    buf: *const libc::c_uchar,
    len: *mut usize,
) -> *mut libc::c_void {
    assert!(!len.is_null());
    let asocket = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };
    let buf: &[u8] = unsafe {
        assert!(!buf.is_null());
        core::slice::from_raw_parts(buf, *len)
    };
    let fd: RawFd = byte2_to_int_offset(buf, 0).into();
    match socket::socket_receive(&mut asocket.hmap, fd) {
        Ok(UDPMessage(buff, size, addr)) => {
            let mut addr_vec = addr.to_string().as_bytes().to_owned();
            let addr_vec_len = addr_vec.len();
            log!("[rs asocket_receive] addr length {}, addr vec {:?}", addr_vec_len, addr_vec);
            let totalsize = size + addr_vec_len;
            unsafe {
                *len = totalsize + 6;
            }
            log!("[rs asocket_receive] totalsize {}", totalsize);
            // message code, total size, addr size
            let mut ret_buf = vec![0, 0, 0, 0, 0, 0];
            int_to_byte2_offset(13, &mut ret_buf, 0);
            int_to_byte2_offset(totalsize as i16, &mut ret_buf, 2);
            int_to_byte2_offset(addr_vec_len as i16, &mut ret_buf, 4);
            ret_buf.append(&mut addr_vec);

            ret_buf.extend_from_slice(&buff);
            slice_to_malloc_buf(&ret_buf)
        }
        Ok(Message(buff, size)) => {
            unsafe {
                *len = size + 4;
            }
            log!("[rs asocket_receive] Message size {}", size);
            // set header
            let mut ret_buf = vec![0, 0, 0, 0];
            int_to_byte2_offset(11, &mut ret_buf, 0);
            int_to_byte2_offset(size as i16, &mut ret_buf, 2);

            ret_buf.extend_from_slice(&buff);
            slice_to_malloc_buf(&ret_buf)
        }
        Ok(MarkShutdown) => {
            unsafe {
                *len = 6;
            }
            log!("[rs asocket_receive] MarkShutdown");
            // set header
            let mut ret_buf = vec![0, 0, 0, 0];
            int_to_byte2_offset(12, &mut ret_buf, 0);
            int_to_byte2_offset(2_i16, &mut ret_buf, 2);

            slice_to_malloc_buf(&ret_buf)
        }
        Ok(NewClient(fd)) => {
            unsafe {
                *len = 6;
            }
            log!("[rs asocket_receive] NewClient");
            // set header
            let mut ret_buf = vec![0, 0, 0, 0, 0, 0];
            int_to_byte2_offset(10, &mut ret_buf, 0);
            int_to_byte2_offset(2_i16, &mut ret_buf, 2);

            int_to_byte2_offset(fd as i16, &mut ret_buf, 4);
            slice_to_malloc_buf(&ret_buf)
        }
        Err(str) => {
            log!("[rs asocket_receive] Error {}", str);
            let str_len = str.len();
            let mut str_vec = str.into_bytes();
            unsafe {
                *len = str_len + 4;
            }
            // TODO refine error code
            // (error kind : w2) (len : w2) message string
            let mut ret_buf = vec![0, 0, 0, 0];
            int_to_byte2_offset(-1_i16, &mut ret_buf, 0);
            int_to_byte2_offset(str_len.try_into().unwrap(), &mut ret_buf, 2);
            ret_buf.append(&mut str_vec);
            slice_to_malloc_buf(&ret_buf)
        }
    }
}

/// ```rs
/// pub fn socket_send (
///     fd_map : &mut std::collections::HashMap<RawFd,Kind>,
///     fd : RawFd,
///     msg : &[u8; MAXMSGSIZE],
/// ) -> Result<(),String> {
/// ```

#[no_mangle]
pub extern "C" fn asocket_send(
    ptr: *mut ASocket,
    buf: *const libc::c_uchar,
    len: *mut usize,
) -> *mut libc::c_void {
    let asocket = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };
    let buf: &[u8] = unsafe {
        assert!(!buf.is_null());
        core::slice::from_raw_parts(buf, *len)
    };
    unsafe {
        assert!(*len >= 4);
    }
    let fd = byte2_to_int_offset(buf, 0);
    let len_header = byte2_to_int_offset(buf, 2) as usize;
    log!(
        "[rs asocket_send] send {:?} bytes over fd {:?}",
        len_header, fd
    );
    unsafe {
        assert!(4 + len_header <= *len);
    }
    let mut msg = [0; socket::MAXMSGSIZE];
    msg[..(socket::MAXMSGSIZE.min(len_header))]
        .clone_from_slice(&buf[4..(socket::MAXMSGSIZE.min(len_header + 4))]);
    unsafe {
        *len = 2;
    }
    match socket::socket_send(&mut asocket.hmap, fd as RawFd, &msg) {
        Ok(()) => {
            log!("[rs socket_send] Ok");
            slice_to_malloc_buf(&[0, 0])
        },
        Err(str) => {
            log!("[rs socket_send] Err {}", str);
            slice_to_malloc_buf(&[0, 1])
        }
    }
}

/// ```rs
/// pub fn socket_send_udp(
///     fd_map: &mut std::collections::HashMap<RawFd, Kind>,
///     fd: RawFd,
///     addr: SocketAddr,
///     msg: &[u8; MAXMSGSIZE],
/// ) -> Result<(), String> {
/// ```

#[no_mangle]
pub extern "C" fn asocket_send_udp(
    ptr: *mut ASocket,
    buf: *const libc::c_uchar,
    len: *mut usize,
) -> *mut libc::c_void {
    let asocket = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };
    let buf: &[u8] = unsafe {
        assert!(!buf.is_null());
        core::slice::from_raw_parts(buf, *len)
    };
    unsafe { assert!(*len >= 6); }
    let fd = byte2_to_int_offset(buf, 0);
    let buflen = byte2_to_int_offset(buf, 2) as usize;
    let addrlen = byte2_to_int_offset(buf, 4) as usize;
    log!("[rs asocket_send_udp] fd {}", fd);
    log!("[rs asocket_send_udp] buflen {}", buflen);
    log!("[rs asocket_send_udp] addrlen {}", addrlen);
    let addr = match std::str::from_utf8(&buf[6..(addrlen + 6)]) {
        Ok(addr_str) => addr_str,
        Err (_e) => {
            log!(
                "[rs asocket_send_udp] invalid string error parsing address {:?}",
                &buf[6..(addrlen+6)]
            );
            return slice_to_malloc_buf(&[0, 2])
        }
    };
    let addr = match addr.parse::<SocketAddr>() {
        Ok(addr) => addr,
        Err (_e) => {
            log!(
                "[rs asocket_send_udp] invalid address string {:?}",
                addr
            );
            return slice_to_malloc_buf(&[0, 3])
        }
    };
    log!(
        "[rs asocket_send_udp] send {:?} bytes over fd {:?} to addr {}",
        buflen, fd, addr
    );
    unsafe {
        assert!(6 + addrlen + buflen <= *len);
    }
    let mut msg = [0; socket::MAXMSGSIZE];
    msg[..(socket::MAXMSGSIZE.min(buflen))]
        .clone_from_slice(&buf[(6 + addrlen)..(socket::MAXMSGSIZE.min(addrlen + buflen + 6))]);
    unsafe {
        *len = 2;
    }

    match socket::socket_send_udp(&mut asocket.hmap, fd as RawFd, addr, &msg) {
        Ok(()) => {
            log!("[rs socket_send_udp] Ok");
            slice_to_malloc_buf(&[0, 0])
        }
        Err(str) => {
            log!("[rs socket_send_udp] Err {}", str);
            slice_to_malloc_buf(&[0, 1])
        }
    }
}

/// ```rs
/// pub fn socket_close (
///     fd_map : &mut std::collections::HashMap<RawFd,Kind>,
///     fd : RawFd,
/// ) -> Result<(),String> {
/// ```

#[no_mangle]
pub extern "C" fn asocket_close (
    ptr : *mut ASocket,
    fd  : libc::c_int,
) -> libc::c_int {
    let asocket = unsafe{
        assert!(!ptr.is_null());
        &mut *ptr
    };
    match socket::socket_close(&mut asocket.hmap, fd as RawFd) {
        Ok(()) => 0,
        Err(_str) => 1,
    }
}

/// Calls
/// ```rs
/// pub fn select  (
///     fd_map : &mut std::collections::HashMap<RawFd,Kind>,
///     fds    : &[RawFd]
/// ) -> Result <Vec<RawFd>,String> {
/// ```
/// input: `buf = 0:w2  len:w2 (fds:w2)*`
/// output: `buf = errorcode:w2  len:w2 (fds:w2)*`

#[no_mangle]
pub extern "C" fn aselect(
    ptr: *mut ASocket,
    buf: *const libc::c_uchar,
    len: *mut usize,
) -> *mut libc::c_void {
    assert!(!len.is_null());
    let asocket = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };
    let buf: &[u8] = unsafe {
        assert!(!buf.is_null());
        core::slice::from_raw_parts(buf, *len)
    };
    // read buffer length from header
    assert!(4 <= buf.len());
    let len_header = byte2_to_int_offset(buf, 2) as usize;
    log!(
        "[rs aselect] header length {:?}, buf.len {:?}",
        len_header,
        buf.len()
    );
    assert!(4 + len_header <= buf.len());
    let mut fds_new: Vec<i32> = Vec::new();
    for i in 0..(len_header / 2) {
        // header has length 4
        fds_new.push(byte2_to_int_offset(buf, (i * 2) + 4) as i32);
    }

    match socket::select(&mut asocket.hmap, &fds_new) {
        Ok(active_fds) => {
            let buf_len = active_fds.len() * 2;
            unsafe {
                *len = buf_len + 4;
            }
            log!("[rs aselect] active fds {:?}", active_fds);
            // set header
            let mut buf: Vec<u8> = vec![0, 0, 0, 0];
            int_to_byte2_offset(buf_len as i16, &mut buf, 2);
            // set body
            for fd in active_fds {
                buf.extend_from_slice(&(fd as i16).to_be_bytes());
            }
            slice_to_malloc_buf(&buf)
        }
        Err(_str) => {
            unsafe {
                *len = 4;
            }
            let mut buf_ret = vec![0, 0, 0, 0];
            int_to_byte2_offset(-1_i16, &mut buf_ret, 0);
            slice_to_malloc_buf(&buf_ret)
        }
    }
}

/// output: `buf : [u8; 8]`

use std::time::{SystemTime, UNIX_EPOCH};

#[no_mangle]
pub extern "C" fn unix_epoch_secs(
    len: *mut usize,
) -> *mut libc::c_void {
    let buf = match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(n) => n.as_secs().to_le_bytes(),
        Err(_) => 0_u64.to_le_bytes(),
    };
    unsafe {
        *len = 8;
    }
    slice_to_malloc_buf(&buf)
}

#[no_mangle]
pub extern "C" fn get_self(
  // the application state (bound sockets, cli flags, ...)
  ptr: *mut ASocket,
  // output buffer length
  len: *mut usize,
) -> *mut libc::c_void {
  assert!(!ptr.is_null());
  let id = unsafe { &(*ptr).config.id };
  let buf_pre = (*id).serialise();
  assert!(buf_pre.is_some());
  let Some(buf) = buf_pre else { todo!() };
  unsafe {
    *len = buf.len();
  }
  slice_to_malloc_buf(&buf)
}

// Supposedly by Daniel Henry-Mantilla in May 2021
// on the rust user forums
// https://users.rust-lang.org/t/how-to-return-byte-array-from-rust-function-to-ffi-c/18136/16
fn slice_to_malloc_buf(xs: &'_ [u8]) -> *mut libc::c_void {
    use ::core::mem::MaybeUninit as MU;

    // allocation with libc allows to free the memory from c
    let ptr = unsafe { ::libc::malloc(xs.len()) };
    if ptr.is_null() {
        return ptr;
    }
    let dst = unsafe { ::core::slice::from_raw_parts_mut(ptr.cast::<MU<u8>>(), xs.len()) };
    let src = unsafe { ::core::slice::from_raw_parts(xs.as_ptr().cast::<MU<u8>>(), xs.len()) };
    dst.copy_from_slice(src);
    ptr
}

