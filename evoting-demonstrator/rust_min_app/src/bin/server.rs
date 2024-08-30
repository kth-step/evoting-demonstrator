#![allow(
  unused_variables,
  unused_imports,
  dead_code,
  unused_assignments,
  clippy::needless_lifetimes
)]

extern crate libc;

use rust_min_app::deserialise::{
  Netsys_input, Netsys_msg, Netsys_name, Request_id, Requests, Response,
};
use rust_min_app::select::*;
use rust_min_app::*;

use deser_lib::{Deserialise, Serialise};

use std::{
  collections::HashMap,
  ffi::c_uint,
  fs,
  io::{Read, Write},
  net::{IpAddr, Shutdown, SocketAddr, UdpSocket},
  os::fd::AsRawFd,
  os::unix::io::RawFd,
  os::unix::net::{UnixListener, UnixStream},
  path::PathBuf,
  time::Duration,
};

// all buffers have this length
static BUFFER_LENGTH: usize = 38960;
static DEBUG_PRINT_BUF_LEN: usize = 30;

#[derive(Debug)]
enum Kind {
  Listener(UnixListener),
  Stream(UnixStream),
  UDPListener(UdpSocket),
}

// hypercall API

#[cfg(feature = "emulation")]
fn read_rust_file_descriptors() -> (c_uint, c_uint) {
  use std::ffi::OsString;
  use std::os::unix::ffi::OsStringExt;
  // the last 8 arguments contain the pipe
  let args: Vec<OsString> = std::env::args_os().collect();
  assert!(args.len() >= 8);
  let l = (args.len() - 8) as usize;

  let rust_r0: Vec<u8> = args[l + 0].clone().into_vec(); //Byte 0 of read file descriptor.
  let rust_r1: Vec<u8> = args[l + 1].clone().into_vec();
  let rust_r2: Vec<u8> = args[l + 2].clone().into_vec();
  let rust_r3: Vec<u8> = args[l + 3].clone().into_vec();
  let rust_r0: u32 = if rust_r0.len() == 0 {
    0
  } else {
    rust_r0[0] as c_uint
  };
  let rust_r1: u32 = if rust_r1.len() == 0 {
    0
  } else {
    (rust_r1[0] as c_uint) << 8
  };
  let rust_r2: u32 = if rust_r2.len() == 0 {
    0
  } else {
    (rust_r2[0] as c_uint) << 16
  };
  let rust_r3: u32 = if rust_r3.len() == 0 {
    0
  } else {
    (rust_r3[0] as c_uint) << 24
  };
  let rust_r = rust_r0 | rust_r1 | rust_r2 | rust_r3;

  let rust_w0: Vec<u8> = args[l + 4].clone().into_vec(); //Byte 0 of write file descriptor.
  let rust_w1: Vec<u8> = args[l + 5].clone().into_vec();
  let rust_w2: Vec<u8> = args[l + 6].clone().into_vec();
  let rust_w3: Vec<u8> = args[l + 7].clone().into_vec();
  let rust_w0: u32 = if rust_w0.len() == 0 {
    0
  } else {
    rust_w0[0] as c_uint
  };
  let rust_w1: u32 = if rust_w1.len() == 0 {
    0
  } else {
    (rust_w1[0] as c_uint) << 8
  };
  let rust_w2: u32 = if rust_w2.len() == 0 {
    0
  } else {
    (rust_w2[0] as c_uint) << 16
  };
  let rust_w3: u32 = if rust_w3.len() == 0 {
    0
  } else {
    (rust_w3[0] as c_uint) << 24
  };
  let rust_w = rust_w0 | rust_w1 | rust_w2 | rust_w3;

  //    println!("r {:?}", rust_r);
  //    println!("w {:?}", rust_w);
  return (rust_r, rust_w);
}

#[cfg(feature = "emulation")]
extern "C" {
  fn invoke_cake(
    output_buffer: *const u64,
    output_buffer_size: u64,
    buffer: *mut u64,
    buffer_size: *mut u64,
    read_fd: c_uint,
    write_fd: c_uint,
  );
}

#[cfg(not(feature = "emulation"))]
extern "C" {
  fn invoke_cake(
    output_buffer: *const u32,
    output_buffer_size: u32,
    buffer: *mut u32,
    buffer_size: *mut u32,
  );
}

// send and receive in the same buffer
fn hypercall_wrap(buf: &mut Data) {
  println!("[rs hypercall_wrap] invoke_cake");
  #[cfg(feature = "emulation")]
  {
    buf.resize(BUFFER_LENGTH, 0);
    let mut buf_len = buf.len() as u64;
    let buf_ptr = buf.as_mut_ptr().cast();
    let (read_fd, write_fd) = read_rust_file_descriptors();
    unsafe { invoke_cake(buf_ptr, buf_len, buf_ptr, &mut buf_len, read_fd, write_fd) };
    println!("[rs hypercall_wrap] return from invoke_cake");
    println!(
      "[rs hypercall_wrap] truncate buffer to length {:?}",
      buf_len
    );
    assert!(buf_len as u32 <= buf.capacity() as u32);
    buf.truncate(buf_len as usize);
  }
  #[cfg(not(feature = "emulation"))]
  {
    buf.resize(BUFFER_LENGTH, 0);
    let mut buf_len = buf.len() as u32;
    let buf_ptr = buf.as_mut_ptr().cast();
    unsafe { invoke_cake(buf_ptr, buf_len, buf_ptr, &mut buf_len) };
    println!("[rs hypercall_wrap] return from invoke_cake");
    println!(
      "[rs hypercall_wrap] truncate buffer to length {:?}",
      buf_len
    );
    assert!(buf_len <= buf.capacity() as u32);
    buf.truncate(buf_len as usize);
  }
}

// end hypercall API

// networking

type FDMap = HashMap<RawFd, Kind>;

struct Conns {
  name: Netsys_name,
  ip: IpAddr,
  port: u16,
  // socket for the single UDP server
  fd_network: RawFd,
  // fds that signaled a change
  fds_queue: Vec<RawFd>,
  // direct Unix Domain input to this node
  has_unix_domain_listener: bool,
  // store for accepted connections from network
  fdmap: FDMap,
  // store of name -> ip:port assignments
  nodes: Vec<(Netsys_name, IpAddr, u16)>,
  // client fds that are marked for closure:
  // When answering a client over Unix Domain Socket the connection is marked for closure, likewise
  // when the client requests a shutdown. If the client fd had been present in fds_closed before,
  // then the connection will be terminated.
  fds_closed: Vec<RawFd>,
  // clients with open connection
  fds_input: Vec<RawFd>,
}

fn socket_create(fdmap: &mut FDMap, socket_file: &PathBuf) -> RawFd {
  // remove socket if exists
  let _ = fs::remove_file(socket_file);
  let mess = &format!(
    "rs socket_create: failed to create socket file {}",
    &socket_file.display()
  );
  let listener = UnixListener::bind(socket_file).expect(mess);
  let raw_fd = listener.as_raw_fd();
  listener
    .set_nonblocking(true)
    .expect("Couldn't set non-blocking");
  fdmap.insert(raw_fd, Kind::Listener(listener));
  println!(
    "[rs socket_create] socket at file {} for fd {:?}",
    &socket_file.display(),
    raw_fd
  );
  raw_fd
}

fn socket_create_udp(fdmap: &mut FDMap, name: &str) -> RawFd {
  let mess = &format!("rs failed to bind to {}", &name);
  let socket = UdpSocket::bind(name).expect(mess);
  socket
    .set_read_timeout(Some(Duration::new(1, 0)))
    .expect("Couldn't set read timeout");
  let raw_fd = socket.as_raw_fd();
  println!(
    "[rs socket_create_udp] socket name {} for fd {:?}",
    name, raw_fd
  );
  fdmap.insert(raw_fd, Kind::UDPListener(socket));
  raw_fd
}

fn socket_close(fdmap: &mut FDMap, fd: RawFd) {
  match fdmap.remove(&fd) {
    None => {
      println!("[rs socket_close] connection for fd {} unknown", fd);
    }
    Some(Kind::Stream(conn)) => {
      println!("[rs socket_close] shutdown connection for fd {}", fd);
      let _ = conn.shutdown(Shutdown::Both);
    }
    Some(Kind::Listener(_)) => {
      println!("[rs socket_close] will not close UnixDomain listener");
    }
    Some(Kind::UDPListener(_)) => {
      println!("[rs socket_close] will not close UDP socket");
    }
  }
}

fn socket_send_udp(
  fdmap: &mut FDMap,
  fd: &RawFd,
  socket_addr: SocketAddr,
  buff: &Data,
) -> Option<()> {
  let len = buff.len();
  println!("[rs socket_send_udp] sending data[{len}] to addr {socket_addr} via UDP");
  println_buffer_head_buf("socket_send_udp", "buff", &buff, DEBUG_PRINT_BUF_LEN);
  match fdmap.get_mut(&fd) {
    Some(Kind::UDPListener(socket)) => {
      match socket.send_to(&buff, socket_addr) {
        Ok(len) => {
          if len <= buff.len() {
            println!(
              "[rs socket_send_udp] wrote {} of {} byte(s)",
              len,
              buff.len()
            );
            return Some(());
          }
        }
        Err(e) => println!("[rs socket_send_udp] socket write error {e:?}"),
      }
      return None;
    }
    _ => {
      println!("[rs socket_send_udp] fd {fd} is no stored UdpSocket");
      return None;
    }
  }
}

fn socket_send(fdmap: &mut FDMap, fd: RawFd, buff: &Data) -> Option<()> {
  let len = buff.len();
  println!("[rs socket_send] sending data[{len}] to fd {fd}");
  println_buffer_head_buf("socket_send", "buff", &buff, DEBUG_PRINT_BUF_LEN);
  match fdmap.get_mut(&fd) {
    None => println!("[rs socket_send] fd {fd} not found in hashmap; nothing sent "),
    Some(Kind::Stream(conn)) => {
      println!("[rs socket_send] Kind::Stream");
      if let Ok(Some(err)) = conn.take_error() {
        println!("[rs socket_send] stream error {err:?}");
        return None;
      }
      match conn.write(&buff) {
        Ok(len) => {
          if len < buff.len() {
            println!("[rs socket_send] wrote {} of {} byte(s)", len, buff.len())
          } else {
            return Some(());
          }
        }
        Err(e) => println!("[rs socket_send] stream write error {e:?}"),
      }
    }
    Some(Kind::Listener(_)) => println!(
      "[rs socket_send] error can only write to Stream, fd {} is a Listener",
      fd
    ),
    Some(Kind::UDPListener(_)) => println!(
      "[rs socket_send] error can only write to Stream, fd {} is a UDPListener",
      fd
    ),
  }
  return None;
}

// End networking

type Data = Vec<u8>;

fn main() {
  // the buffer for input/output data
  let mut data = vec![0; BUFFER_LENGTH];

  let mut nodes = vec![];
  let mut debug_level = 0;
  let mut name: Netsys_name = Default::default();
  let mut path_buf_opt: Option<PathBuf> = None;

  #[cfg(feature = "emulation")]
  {
    let mut args = std::env::args();
    cli::parse(
      &mut args,
      &mut nodes,
      &mut name,
      &mut debug_level,
      &mut path_buf_opt,
    );
  }

  #[cfg(not(feature = "emulation"))]
  {
    use core::net::{IpAddr, Ipv4Addr};
    name = Netsys_name::Name_VCS;
    nodes = vec![
      (Netsys_name::Name_VCS,    IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)),8080,),
      (Netsys_name::Name_Admin,  IpAddr::V4(Ipv4Addr::new(192, 100, 1, 1)), 8081,),
      (Netsys_name::Name_MixNet, IpAddr::V4(Ipv4Addr::new(192, 100, 1, 1)), 8082,),
      (Netsys_name::Name_Client, IpAddr::V4(Ipv4Addr::new(192, 100, 1, 1)), 8083,),
    ];
    path_buf_opt = None;
    debug_level = 3;
  }

  println!("[rs main] CLI argument parse result");
  println!("[rs main] nodes: {:?}", nodes);
  println!("[rs main] name: {:?}", name);
  println!("[rs main] direct input socket: {:?}", path_buf_opt);

  // Connection setup
  // let mut data = Vec::<u8>::with_capacity(BUFFER_LENGTH);
  // let name = Netsys_name::Name_VCS;
  data[0] = name.serialise().unwrap()[0];
  let mut fdmap = HashMap::new();

  // start own server
  let (ip, port) = lookup_name(&nodes, &name).expect("cannot find {name:?} in {nodes:?}");
  let udp_name_client = format!("{ip}:{port}");
  let fd_network = socket_create_udp(&mut fdmap, &udp_name_client);
  println!(
    "[rs main] started server at address {} (via socket_create_udp)",
    udp_name_client
  );
  let has_unix_domain_listener = path_buf_opt.map(|path_buf| socket_create(&mut fdmap, &path_buf)).is_some();

  let mut conns = Conns {
    name,
    ip,
    port,
    fd_network,
    fds_queue: vec![],
    has_unix_domain_listener,
    fdmap,
    nodes,
    fds_closed: vec![],
    fds_input: vec![],
  };

  let mut i = 0;
  loop {
    // only temporarily
    if i == 5 {
      println!("[rs main] break loop at iteration {i}");
      break;
    };
    i += 1;

    println!("[rs main] loop iteration {i}");
    hypercall_wrap(&mut data);
    send_response_to_network(&mut conns, &data);
    std::thread::sleep(Duration::from_millis(1000));
    get_network_input(&mut conns, &mut data);
  }
}

fn println_buffer_head_vec(fun: &str, tag: &str, buffer: &Data, max: usize) {
  if max == 0 {
    return;
  }
  let len = std::cmp::min(max, buffer.len());
  print!("[rs {fun}] {tag}[..{len}] = [");
  for x in buffer.clone().iter().take(len) {
    print!("{:x}; ", x);
  }
  println!("]");
}

fn println_buffer_head_buf(fun: &str, tag: &str, buffer: &[u8], max: usize) {
  if max == 0 {
    return;
  }
  let len = std::cmp::min(max, buffer.len());
  print!("[rs {fun}] {tag}[..{len}] = [");
  for x in buffer.iter().take(len) {
    print!("{:x}; ", x);
  }
  println!("]");
}

// sends responses to network and unix domain socket
fn send_response_to_network(conns: &mut Conns, data: &Data) {
  println!("[rs send_response_to_network] entering method");
  // TODO make client serialise the message and
  // change Response to:
  //Response {
  //Response(u64, Vec<(Netsys_name, Vec<u8>)>),
  //DeserialiseFail,
  //}

  match Response::deserialise(data) {
    Some((Response::Response(id, msgs), _n)) => {
      // output_handler
      // send response(s)
      println!("[rs send_response_to_network] response id {id}");

      for (target, msg) in msgs {
        let msg_copy = msg.clone();
        eprintln!(
          "[rs send_response_to_network] target {:?} msg: {:?}",
          target, msg
        );
        let msg_buf = msg
          .serialise()
          .expect("[rs send_response_to_network] cannot serialise msg");
        // TODO pad_msg
        // let msg_buf = (msg_buf);
        // assert_eq!(msg_buf.len(), BUFFER_LENGTH);

        // message with target self are sent over input socket
        if target == conns.name {
          println!("[rs send_response_to_network] reading a message to self == output over Unix Domain input socket");
          if conns.has_unix_domain_listener {
            eprintln!(
              "[rs send_response_to_network] ignore input msg: no input socket"
            );
            continue;
          }

          // determine the file descriptor (which is the message id)
          let id_opt = if conns.fds_input.contains(&(id as RawFd)) {
            println!("[rs send_response_to_network] use response header id {id}");
            Some(id as RawFd)
          } else {
            let id_opt: Option<u64> = msg_id(&msg_copy).copied();
            if id_opt.is_some() && conns.fds_input.contains(&(id_opt.unwrap() as RawFd)) {
              println!(
                "[rs send_response_to_network] use message header id {}",
                id_opt.unwrap()
              );
              Some(id_opt.unwrap() as RawFd)
            } else {
              println!("[rs send_response_to_network] no id found");
              None
            }
          };

          // no broadcasting
          if let Some(id) = id_opt {
            // answer to the particular request id
            eprintln!(
              "[rs send_response_to_network] send msg to id {:?} (no broadcast)",
              id
            );

            match socket_send(&mut conns.fdmap, id, &msg_buf) {
              Some(_) => {
                // TODO Any connection from fds_input should be closed after client has received an answer
                if conns.fds_closed.contains(&id) {
                  println!("[rs send_response_to_network] close connection to {id}");
                  socket_close(&mut conns.fdmap, id);
                  conns.fds_closed.retain(|fd| !fd == id);
                  conns.fds_input.retain(|fd| !fd == id);
                } else {
                  conns.fds_closed.push(id);
                  println!(
                    "[rs send_response_to_network] mark {id} for closure (add to conns.fds_closed)"
                  );
                }
                println!(
                  "[rs send_response_to_network] conns.fds_input {:?}",
                  conns.fds_input
                );
                println!(
                  "[rs send_response_to_network] conns.fds_closed {:?}",
                  conns.fds_closed
                );
              }
              _ => continue,
            };
          } else {
            eprintln!(
              "[rs send_response_to_network] broadcast msg to every conns.fds_input {:?}",
              conns.fds_input
            );
            eprintln!("[rs send_response_to_network] target msg: {:?}", msg_copy);
            // broadcast to all socket fds as no particular request id was found
            let input_fds_iter = conns.fds_input.clone();
            let close_fds = input_fds_iter.iter().filter(|&fd| {
              match socket_send(&mut conns.fdmap, *fd, &msg_buf) {
                Some(_) => {
                  if conns.fds_closed.contains(&(*fd as RawFd)) {
                    socket_close(&mut conns.fdmap, *fd);
                  }
                  true
                }
                _ => false,
              }
            });
            let closed_fds: Vec<_> = close_fds.collect();
            // keep fds that were not closed
            eprintln!(
              "[rs send_response_to_network] the fds that were just marked for closure {:?}",
              closed_fds
            );
            conns.fds_closed.retain(|fd| !closed_fds.contains(&fd));
            eprintln!(
              "[rs send_response_to_network] diminish conns.fds_closed to {:?}",
              conns.fds_closed
            );
            conns.fds_input.retain(|fd| !closed_fds.contains(&fd));
            eprintln!(
              "[rs send_response_to_network] diminish conns.fds_input to {:?}",
              conns.fds_input
            );
          }
        // target != conns.name
        } else {
          // send over network
          if let Some(ip_port) = lookup_name(&conns.nodes, &target) {
            let _succ = socket_send_udp(
              &mut conns.fdmap,
              &conns.fd_network,
              ip_port.into(),
              &msg_buf,
            );
          } else {
            println!(
              "[rs send_response_to_network] ignore network msg: unknown destination {:?}",
              target
            );
          }
        }
      }
    }
    _ => println!(
      "[rs send_response_to_network] send no responses: deserialisation failed for data[{}]",
      data.len()
    ),
  }
}

// waits until data is received
fn get_network_input(conns: &mut Conns, data: &mut Data) {
  loop {
    if conns.fds_queue.is_empty() {
      // accept new messages from network
      // prepare list of fds to listen to
      conns.fds_queue = conns.fdmap.keys().cloned().collect::<Vec<i32>>();
      /*
      for fd in conns.fdmap.keys() {
        // listen also to fds that are marked for closure
        conns.fds_queue.push(*fd);
      }
      */

      println!(
        "[rs get_network_input] select with: let conns.fds_queue = {:?};",
        &conns.fds_queue
      );
      match my_select(&conns.fdmap, &mut conns.fds_queue) {
        Ok(()) => {
          if conns.fds_queue.is_empty() {
            println!("[rs get_network_input] no fds active");
            std::thread::sleep(Duration::from_millis(2000));
            continue; // will run select again
          } else {
            println!("[rs get_network_input] active fds: {:?}", conns.fds_queue);
          }
        }
        Err(e) => {
          println!("[rs get_network_input] select error {:?}", e);
          continue;
        }
      }
    }
    let mut has_data_changed = false;
    let queue_ = conns.fds_queue.clone();
    println!("[rs get_network_input] handle queue {:?}", queue_);
    // consume queue_ until has_data_changed becomes true
    let queue_rest = queue_.iter().skip_while(|&active_fd| {
      println!("[rs get_network_input] next fd in queue {}", active_fd);
      has_data_changed = socket_receive(conns, *active_fd, data);
      println!("[rs get_network_input] after socket_receive over fd {active_fd}: data received? {has_data_changed:?}");
      has_data_changed
    });
    // collect the remaining active_fds
    // skip first on which socket_receive returned true
    conns.fds_queue = queue_rest.skip(1).copied().collect::<Vec<_>>();
    println!(
      "[rs get_network_input] remaining fd queue {:?}",
      conns.fds_queue
    );
    if has_data_changed {
      return;
    } else {
      println!("[rs get_network_input] no change of data");
    }
  } // loop
}

// TODO preset buffer full header
// FIXME drop comment: combines earlier socket_receive and receiver_state_change
// returns Some if a message was read into data
fn socket_receive(conns: &mut Conns, fd: RawFd, data: &mut Data) -> bool {
  let mut data_len_new = 0usize;
  match conns.fdmap.get_mut(&fd) {
    None => {
      println!("[rs socket_receive] connection for fd {} unknown", fd);
    }
    // receive content
    Some(Kind::Stream(stream)) => {
      // should read and return the message
      stream
        .set_read_timeout(Some(Duration::new(1, 0)))
        .expect("Couldn't set read timeout");
      // Requests::Input_direct (id, _)
      // test_len_request_serialise_input_direct
      data.resize(BUFFER_LENGTH, 0);
      let header_direct_len = 9usize;
      let (header, body) = data.split_at_mut(header_direct_len);
      match stream.read(body) {
        Ok(0) => {
          // client disconnects, keep connection in order to send an answer
          println!(
            "[rs socket_receive] Kind::Stream: mark shutdown client writer fd {}",
            fd
          );
          // mark for shutdown
          if !conns.fds_closed.contains(&fd) {
            conns.fds_closed.push(fd);
            println!(
              "[rs socket_receive] added fd to conns.fds_closed {:?}",
              conns.fds_closed
            );
          } else {
            println!(
              "[rs socket_receive] Shutdown received and fd {fd} was marked for closure before"
            );
            socket_close(&mut conns.fdmap, fd);
            conns.fds_closed.retain(|fd_| !fd == *fd_);
            conns.fds_input.retain(|fd_| !fd == *fd_);
          }
          data_len_new = 0;
        }
        Ok(len) => {
          println!("[rs socket_receive] Kind::Stream: fd {} len {}", fd, len);
          println_buffer_head_buf("socket_receive", "header", header, DEBUG_PRINT_BUF_LEN);
          println_buffer_head_buf("socket_receive", "body", body, DEBUG_PRINT_BUF_LEN);
          data_len_new = len + header_direct_len;
          // Requests::Input_direct (id.into(), )
          // test_len_request_serialise_input_direct
          let fd_bytes = (fd as u64).to_be_bytes();
          println!(
            "[rs socket_receive] set header request id to fd {:?}",
            fd_bytes
          );
          assert!(header_direct_len == fd_bytes.len() + 1);
          // header[0] = 0;
          for (p, x) in header
            .iter_mut()
            .take(header_direct_len)
            .skip(1)
            .enumerate()
          {
            *x = fd_bytes[p];
          }
        }
        Err(e) => {
          println!(
            "rs socket_receive Kind::Stream: unkown error reading from stream fd {} {:?}",
            fd, e
          );
        }
      }
    }
    // receive connection
    Some(Kind::Listener(listener)) => match listener.accept() {
      Ok((conn, _addr)) => {
        println!(
          "[rs socket_receive] Kind::Listener: new client conn: {:?}",
          conn
        );
        conn
          .set_nonblocking(true)
          .expect("Couldn't set non-blocking");
        let fd_new = conn.as_raw_fd();
        conns.fdmap.insert(fd_new, Kind::Stream(conn));
        conns.fds_input.push(fd_new);
        conns.fds_closed.retain(|fd| fd != &fd_new); // drop new client from list
        println!("[rs socket_receive] conns.fds_input {:?}", conns.fds_input);
        data_len_new = 0;
      }
      Err(e) => {
        println!("rs socket_receive Kind::Listener: unkown error receiving client from listener fd {} {:?}", fd, e);
      }
    },
    // receive UDP connection
    Some(Kind::UDPListener(socket)) => {
      // Requests::Input_network(msg_id,name,msg)
      // test_len_request_serialise_input_network
      let header_input_network_len = 10usize;
      // alternative to split_at_mut is Vec::spare_capacity_mut
      data.resize(BUFFER_LENGTH, 0);
      let (header, body) = data.split_at_mut(header_input_network_len);
      println!("[rs socket_receive] Kind::UDPListener: {:?}", socket);
      // should read and return the message
      match socket.recv_from(body) {
        Ok((len, addr)) => {
          println!(
            "[rs socket_receive] Kind::UDPListener fd {} len {} from {:?}",
            fd, len, addr
          );
          data_len_new = len + header_input_network_len;
          println_buffer_head_buf("socket_receive", "header", header, DEBUG_PRINT_BUF_LEN);
          println_buffer_head_buf("socket_receive", "body", body, DEBUG_PRINT_BUF_LEN);
          if len == BUFFER_LENGTH {
            println!("[rs socket_receive] received exactly {BUFFER_LENGTH} bytes. More data might be available.");
          }
          // sets header: header[0..<header_input_network_len] = Requests::Input_network(id, name, _)
          header[0] = 1;
          for x in header.iter_mut().skip(1) {
            *x = 0u8;
          }
          // TODO get msg_id
          let msg_id = fd; // msg_id(&body.deserialise());
          int_to_byte2_offset(msg_id as i16, header, header_input_network_len - 3);
          match lookup_addr(&conns.nodes, &addr.ip(), &addr.port()) {
            None => println!("[rs socket_receive] unknown sender address {addr}"),
            Some(name) => {
              header[header_input_network_len - 1] = name.serialise().unwrap()[0];
            }
          }
        }
        Err(e) => {
          data_len_new = 0;
          println!(
            "rs socket_receive Kind::UDPListener: unkown error reading from UDP fd {} {:?}",
            fd, e
          );
        }
      }
    }
  } // match val
  data.truncate(data_len_new);
  data_len_new != 0 // success iff an actual message was written
}

fn my_select(fdmap: &FDMap, fds: &mut Vec<RawFd>) -> Result<(), String> {
  if fds.is_empty() {
    return Ok(());
  }
  fds.dedup();
  if fdmap.is_empty() {
    return Err(format!(
      "rs my_select: trying to select {:?} from {} connections",
      fds,
      fdmap.len()
    ));
  }
  // gets the maximal file descriptor
  let (max_fd, _) = &fdmap
    .iter()
    .max_by(|(a, _v), (b, _w)| a.partial_cmp(b).unwrap())
    .unwrap();

  // prepares the set of file descriptors for FdSet
  let mut fd_set = select::FdSet::new();
  for fd in &mut *fds {
    if fdmap.contains_key(fd) {
      fd_set.set(*fd);
    }
  }

  let timeout = Duration::new(10, 0);
  match select::pselect(
    *max_fd + 1,
    Some(&mut fd_set), // read
    None,              // write
    None,              // error
    Some(timeout),     // timeout
    None,              // mask
  ) {
    // no activity
    Ok(0) => {
      fds.clear();
    }
    Err(e) => {
      fds.clear();
      return Err(format!("rs my_select: failed to select: {:?}", e));
    }
    // no of active file descriptors
    Ok(num) => {
      println!("[rs my_select] number of active fds {}", num);
      fds.retain(|&fd| {
        if (fd_set).is_set(fd) {
          println!("[rs my_select] active fd {:?}", fd);
          true
        } else {
          false
        }
      });
    }
  }
  Ok(())
}

fn adjust_id(msg: Netsys_input, id: u64) -> Netsys_input {
  match msg {
    Netsys_input::Input_Ballot(sign, _rid, vote) => {
      Netsys_input::Input_Ballot(sign, deserialise::Request_id::Request(id), vote)
    }
    x => x,
  }
}

fn msg_id(x: &Netsys_msg) -> Option<&u64> {
  match x {
    Netsys_msg::Msg_Ballot(_sign, rid, _vote) => Some(request_id_id(rid)),
    Netsys_msg::Msg_BallotRecorded(rid, _voter) => Some(request_id_id(rid)),
    Netsys_msg::Msg_BallotError(rid) => Some(request_id_id(rid)),
    Netsys_msg::Msg_Response(rid, _data) => Some(request_id_id(rid)),
    _ => None,
  }
}

fn lookup_addr(
  nodes: &[(Netsys_name, IpAddr, u16)],
  ip: &IpAddr,
  port: &u16,
) -> Option<Netsys_name> {
  nodes
    .iter()
    .position(|(_, n_ip, n_port)| &(n_ip, n_port) == &(ip, port))
    .map(|n| nodes[n].0)
}

fn lookup_name(nodes: &[(Netsys_name, IpAddr, u16)], name: &Netsys_name) -> Option<(IpAddr, u16)> {
  nodes
    .iter()
    .position(|&r| r.0 == *name)
    .map(|n| (nodes[n].1, nodes[n].2))
}

fn request_id_id(x: &Request_id) -> &u64 {
  use crate::deserialise::Request_id::Request;
  let Request(id) = x;
  id
}

#[cfg(test)]
mod tests {

  use super::*;
  #[test]
  fn test_len_request_serialise_input_direct() {
    // length = 9usize
    let req = Requests::Input_direct(1, Netsys_input::Input_VotingStart(vec![]));
    let buf = Some(vec![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]);
    assert_eq!(req.serialise(), buf);
  }

  #[test]
  fn test_len_request_serialise_input_network() {
    // length = 10usize
    let req = Requests::Input_network(220, Netsys_name::Name_Client, Netsys_msg::Msg_Confirm);
    let buf = Some(vec![1, 0, 0, 0, 0, 0, 0, 0, 220, 3, 7]);
    assert_eq!(req.serialise(), buf);
  }
} // mod test
