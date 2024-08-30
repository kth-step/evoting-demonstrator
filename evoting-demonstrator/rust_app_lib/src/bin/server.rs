#![allow(unused_imports)]

use rust_app_lib::*;
use rust_app_lib::deserialise::{Requests,Response,Request_id,Netsys_name,Netsys_msg,Netsys_input};
use rust_app_lib::socket::Receive::{NewClient,Message,UDPMessage,MarkShutdown};
use deser_lib::{Serialise,Deserialise};

use core::ffi::c_uint;
use std::os::unix::io::RawFd;
use core::net::IpAddr;

const BUFFER_SIZE : usize = 38960;

// https://github.com/rust-lang/rust/issues/88345
#[allow(non_camel_case_types)]
pub type c_size_t = usize;

// #[link(name = "invoke_cake", kind = "static")]
#[cfg(feature = "emulation")]
extern "C" {
  fn invoke_cake(
    output_buffer      : *const u64,
    output_buffer_size :        u64,
    input_buffer       :   *mut u64,
    input_buffer_size  :   *mut u64,
    read_fd : c_uint,
    write_fd : c_uint);
}

#[cfg(not(feature = "emulation"))]
extern "C" {
  fn invoke_cake(
    output_buffer      : *const u32,
    output_buffer_size :        u32,
    input_buffer       :   *mut u32,
    input_buffer_size  :   *mut u32,
  );
}

#[cfg(feature = "emulation")]
fn read_rust_file_descriptors() -> (c_uint, c_uint) {
  use std::ffi::OsString;
  use std::os::unix::ffi::OsStringExt;
  // the last 8 arguments contain the pipe
  let args: Vec<OsString> =  std::env::args_os().collect();
  assert!(args.len() >= 8);
  let l = (args.len() - 8) as usize;

  let rust_r0: Vec<u8> = args[l+0].clone().into_vec();	//Byte 0 of read file descriptor.
  let rust_r1: Vec<u8> = args[l+1].clone().into_vec();
  let rust_r2: Vec<u8> = args[l+2].clone().into_vec();
  let rust_r3: Vec<u8> = args[l+3].clone().into_vec();
  let rust_r0: u32 = if rust_r0.len() == 0 {0} else {rust_r0[0] as c_uint};
  let rust_r1: u32 = if rust_r1.len() == 0 {0} else {(rust_r1[0] as c_uint) << 8};
  let rust_r2: u32 = if rust_r2.len() == 0 {0} else {(rust_r2[0] as c_uint) << 16};
  let rust_r3: u32 = if rust_r3.len() == 0 {0} else {(rust_r3[0] as c_uint) << 24};
  let rust_r = rust_r0 | rust_r1 | rust_r2 | rust_r3;

  let rust_w0: Vec<u8> = args[l+4].clone().into_vec();	//Byte 0 of write file descriptor.
  let rust_w1: Vec<u8> = args[l+5].clone().into_vec();
  let rust_w2: Vec<u8> = args[l+6].clone().into_vec();
  let rust_w3: Vec<u8> = args[l+7].clone().into_vec();
  let rust_w0: u32 = if rust_w0.len() == 0 {0} else {rust_w0[0] as c_uint};
  let rust_w1: u32 = if rust_w1.len() == 0 {0} else {(rust_w1[0] as c_uint) << 8};
  let rust_w2: u32 = if rust_w2.len() == 0 {0} else {(rust_w2[0] as c_uint) << 16};
  let rust_w3: u32 = if rust_w3.len() == 0 {0} else {(rust_w3[0] as c_uint) << 24};
  let rust_w = rust_w0 | rust_w1 | rust_w2 | rust_w3;

//    println!("r {:?}", rust_r);
//    println!("w {:?}", rust_w);
  return (rust_r, rust_w);
}

fn hypercall_wrap(output_buffer: Vec<u8>, input_buffer: &mut Vec<u8>) {

  println!("[rs hypercall_wrap] hypercall_wrap(output_buffer, input_buffer)");
  assert!(input_buffer.len() <= BUFFER_SIZE);
  assert!(output_buffer.len() <= BUFFER_SIZE);

  #[cfg(feature = "emulation")]
  let mut input_buffer_size = input_buffer.len() as u64;

  #[cfg(feature = "emulation")]
  {
    let (read_fd, write_fd) = read_rust_file_descriptors();
    println!("[rs hypercall_wrap] read_fd {:?}, write_fd {:?}", read_fd, write_fd);
    unsafe {
      let ptr_out = output_buffer.as_ptr().cast();
      let ptr_in = input_buffer.as_mut_ptr().cast();
      println!("[rs hypercall_wrap] output_buffer ptr {:?}", ptr_out);
      println!("[rs hypercall_wrap] output_buffer.len() {:?}", output_buffer.len());
      println!("[rs hypercall_wrap] input_buffer ptr {:?}", ptr_in);
      println!("[rs hypercall_wrap] input_buffer.len() {:?}", input_buffer.len());
      print!("[rs hypercall_wrap] output_buffer data:");

      for x in output_buffer.iter().take(30) {
        print!(" {:x}", x);
      }
      println!("");
      println!("[rs hypercall_wrap] call to invoke_cake -- handover to CakeML/C");

      invoke_cake(ptr_out, output_buffer.len() as u64, ptr_in, &mut input_buffer_size, read_fd, write_fd);
      println!("[rs hypercall_wrap] end invoke_cake -- handover from CakeML/C to Rust");
    }
  }

  #[cfg(not(feature = "emulation"))]
  let mut input_buffer_size = input_buffer.len() as u32;
  #[cfg(not(feature = "emulation"))]
  unsafe {
    invoke_cake(output_buffer.as_ptr().cast(), output_buffer.len() as u32, input_buffer.as_mut_ptr().cast(), &mut input_buffer_size)
  }

  println!("[rs hypercall_wrap] truncate input_buffer to length {:?}", input_buffer_size);
  // check that C respected the capacity limit
  assert!(input_buffer_size as u32 <= input_buffer.capacity() as u32);
  // truncate keeps the capacity
  input_buffer.truncate(input_buffer_size as usize);
}

fn main() {
    let a = &mut ASocket::new();
    #[cfg(feature = "emulation")]
    println!("[rs main] pipes: {:?}", a.config.pipes);
    println!("[rs main] verbose: {:?}", a.config.verbose);
    println!("[rs main] nodes: {:?}", a.config.nodes);
    println!("[rs main] id {:?}", a.config.id);

    // first message is the netsys_name
    let get_self = a.config.id.serialise().expect("node id not serialisable");

    #[cfg(not(feature = "emulation"))]
    {
      println!("[rs main] attempt to send to all streams");
      use crate::socket::Kind::{Listener,UDPListener,Stream};
      use std::io::Write;
      // let ip_port = a.config.nodes[2].2;
      let mut buf_end = vec![0,1,0,2,0,3,0,4,0,5,0,6 as u8];
      let mut msg_buf = vec![0, 0, 0, buf_end.len() as u8];
      msg_buf.append(&mut buf_end);
      a.hmap.iter_mut().all(
        |(_raw_fd,v)| match v {
          Listener(_) => true,
          Stream(ref mut s) => {
            println!("[rs main] one connected stream");
            let _ = s.write_all(&msg_buf); true
          },
          UDPListener(_) => true,
          //{let _ = s.send_to(&msg_buf,a.fd_net); true},
      });
      println!("[rs main] after send attempt");
    }

    // println!("rs: self: {:?}", a.config.id.to_string());
    // println!("rs self (buf): {:?}", get_self);
    let mut buf = get_self; // input to hypercall
    let mut in_buf = vec![0; BUFFER_SIZE]; // output from hypercall

    // for i in 0i32..20 {
    let mut i = 0i32;
    for _x in 0..10 {
    // loop {
        println!("[rs main] loop iteration {i}");

  println!("[rs main] before hypercall_wrap (after output_handler_bytes)");
  print!("[rs main] in_buf[..30] = ");
  for x in in_buf.clone().iter().take(30) {
    print!(" {:x}", x);
  }
  println!("");

  print!("[rs main] buf[..30] = ");
  for x in buf.clone().iter().take(30) {
    print!(" {:x}", x);
  }
  println!("");

        println!("[rs main] call to hypercall_wrap(buf, &mut in_buf)");
        hypercall_wrap(buf, &mut in_buf);

        println!("[rs main] handover to rust");
        std::thread::sleep(std::time::Duration::from_millis(1000));

  println!("[rs main] after hypercall_wrap/before output_handler_bytes");
  print!("[rs main] in_buf[..30] = ");
  for x in in_buf.clone().iter().take(30) {
    print!(" {:x}", x);
  }
  println!("");

  println!("[rs main] buf[..30] = unchanged");

        buf = output_handler_bytes(a, &in_buf);
        // in_buf = buf.clone();
        i += 1;
    }
}

fn output_handler(state : &mut ASocket, r : Response) -> Option<Requests> {
  // send response
  match r {
    Response::DeserialiseFail =>
      eprintln!("[rs output_handler] ignore response - failed to deserialise"),
    Response::Response (id, msgs) => {
      for (name,msg) in msgs {
        // try to use the id annotated in the data
        let mut id_opt : Option<u64> = msg_id(&msg).clone().copied();
        let msg_copy = msg.clone();
        eprintln!("[rs output_handler] name {:?} msg: {:?}", name, msg_copy);
        let msg_buf = msg.serialise().expect("[rs output_handler] cannot serialise msg");
        let msg_buf = pad_msg(msg_buf);
        assert_eq!(msg_buf.len(), BUFFER_SIZE);

        // send over socket
        if name == state.config.id {

          if state.fd_input.is_none() {
            eprintln!("[rs output_handler] ignore input msg: no connection to input socket");
            continue;
          }
          eprintln!("[rs output_handler] state.fd_input {}", state.fd_input.unwrap());

          eprintln!("[rs output_handler] request id from message {:?} (vs {:?})", id_opt, id);

          let mut no_broadcast = id_opt.is_some() && state.input_fds.contains(&(id_opt.unwrap() as RawFd));
          // replace id_opt with the id from the response
          if !no_broadcast {
            no_broadcast = state.input_fds.contains(&(id as RawFd));
            eprintln!("[rs output_handler] trying to use Request id instead {:?}: {}", id, no_broadcast);
            id_opt = Some(id);
          }
          eprintln!("[rs output_handler] response from {id} is from a known state.input_fds");

          if no_broadcast {

            let id = id_opt.unwrap() as i32;
            // answer to the particular request id
            eprintln!("[rs output_handler] send msg to id {:?} (no broadcast)", id);

            eprintln!("[rs output_handler] state.fd_input {}", state.fd_input.unwrap());
            match socket::socket_send(&mut state.hmap, id, &msg_buf) {
              Ok(_) => {
                if state.closed_fds.contains(&id) {
                  let _ = socket::socket_close(&mut state.hmap, id);
                }
                state.closed_fds.retain(|fd| !fd == id);
                eprintln!("[rs output_handler] diminish state.closed_fds to {:?}", state.closed_fds);
                state.input_fds.retain(|fd| !fd == id);
                eprintln!("[rs output_handler] diminish state.input_fds to {:?}", state.input_fds);
              },
              _ => continue
            };

          } else {

            eprintln!("[rs output_handler] broadcast msg to state.input_fds {:?}", state.input_fds);
            eprintln!("[rs output_handler] name msg: {:?}", msg_copy);
            // broadcast to all socket fds as no particular request id was found
            let input_fds_iter = state.input_fds.clone();
            let close_fds = input_fds_iter.iter().filter_map(|fd|
                match socket::socket_send(&mut state.hmap, *fd, &msg_buf) {
                Ok(_) => {
                    if state.closed_fds.contains(&(*fd as RawFd)) {
                    let _ = socket::socket_close(&mut state.hmap, *fd);
                    }
                    Some(fd)
                }
                _ => None,
                }
            );
            let closed_fds : Vec<_> = close_fds.collect();
            // keep fds that were not closed
            eprintln!("[rs output_handler] the fds that were just closed {:?}", closed_fds);
            state.closed_fds.retain(|fd| !closed_fds.contains(&fd));
            eprintln!("[rs output_handler] diminish state.closed_fds to {:?}", state.closed_fds);
            state.input_fds.retain(|fd| !closed_fds.contains(&fd));
            eprintln!("[rs output_handler] diminish state.input_fds to {:?}", state.input_fds);
          }
        } else {
          // send over network
          if let Some(ip_port) = lookup_name(&state.config.nodes, &name) {
            let _succ = socket::socket_send_udp(&mut state.hmap, state.fd_net, ip_port.into(), &msg_buf);
          } else {
            eprintln!("[rs output_handler] ignore network msg: unknown destination {:?}", name);
          }
        }
      }
    }
  }

  // receive requests until first message
  for _x in 0..10 {
  // loop {
    let mut fds = vec![];
    for fd in state.hmap.keys() {
      // skip listening to closed fds
      if !state.closed_fds.contains(&(*fd as RawFd)) {
        fds.push(*fd);
      }
    }

    if state.queue.is_empty() {
      match socket::select(&mut state.hmap, &fds) {
        Ok(active_fds) => {
          if active_fds.is_empty() {
            println!("[rs output_handler] no fds active");
            continue; // will run select again
          } else {
            println!("[rs output_handler] active fds: {:?}", active_fds);
          }
          state.queue = active_fds;
        },
        Err(e) => {
          println!("[rs output_handler] select error {:?}", e);
          continue;
        },
      }
    }

    let mut ret_val : Option<Requests> = None;
    let queue_ = state.queue.clone();
    println!("[rs output_handler] handle queue {:?}", queue_);
    // consume queue_ until first receiver_state_change == Some(x)
    let queue_rest = queue_.iter().skip_while(|&active_fd| {
      println!("[rs output_handler] next fd in queue {}", active_fd);
      ret_val = receiver_state_change(state, *active_fd);
      ret_val.is_none()
    });
    // collect the remaining active_fds
    // skip first on which receiver_state_change returned Some
    state.queue = queue_rest.skip(1).copied().collect::<Vec<_>>();
    println!("[rs output_handler] remaining fd queue {:?}", state.queue);
    if ret_val.is_some() {
      return ret_val;
    }
    println!("[rs output_handler] no message value received");
  }
  None
}

pub fn output_handler_bytes(state : &mut ASocket, buf : &[u8]) -> Vec<u8>{
/*
  let buf_data_len = u16::from_be_bytes(buf[0..2].try_into().unwrap()) as usize;
  let strip_header = 0 < buf_data_len && buf_data_len + 2 < buf.len();
  let data =
     if strip_header
      { buf[2..=(buf_data_len+2)].into() }
      else { buf };
*/
  let data = buf;

  // println!("[rs output_handler_bytes] strip header prior deserialisation? {:?}", strip_header);
  print!("[rs output_handler_bytes] data (len {:?}): [", data.len());
  for x in data.iter().take(30) {
    print!("{:}; ", x);
  }
  println!("]");


  let ret_vec =
    match Response::deserialise(data) {
      None => {
        print!("[rs output_handler_bytes] deserialisation failed for buf[{}]", buf.len());
/*
        for x in buf.iter().take(30) {
          print!(" {:x}", x);
        }
*/
        println!("");
        output_handler(state, Response::DeserialiseFail)
      },
      Some((resp,_n)) =>
        // handle output even if the buffer is not completely consumed
        // if n == buf.len() {
        output_handler(state, resp)
/*
        } else {
          eprintln!("[rs output_handler] deserialisation could not consume full buffer");
          None
        }
*/
    };
  match ret_vec.and_then(|x| x.serialise()) {
    Some(v) => v,
    _ => Response::DeserialiseFail.serialise().unwrap(), // vec![0u8], // DeserialiseFail
  }
}

/// Some indicates a message receival
/// None indicates no message receival
fn receiver_state_change(
  state : &mut ASocket,
  active_fd : RawFd
) -> Option<Requests> {
  match socket::socket_receive(&mut state.hmap, active_fd) {
    Ok(MarkShutdown) => {
      println!("[rs receiver_state_change] mark for shutdown fd {}", active_fd);
      state.closed_fds.push(active_fd);
      println!("[rs receiver_state_change] state.closed_fds {:?}", state.closed_fds);
      None
    },
    Ok(UDPMessage(buf, _len, addr)) => {
      print!(
        "[rs receiver_state_change] UDPMessage fd {} socket_receive UDP from addr {:?} (up to 30 chars): [",
        active_fd, addr
        );
      for x in buf.clone().iter().take(30) {
        print!(" {:};", x);
      }
      println!("]");

      if let Some(name) = lookup_addr(&state.config.nodes, addr.to_string()) {
        Netsys_msg::deserialise(&buf).and_then(|(msg,_len)| {
          match msg_id(&msg) {
            Some(id) => {
              println!("[rs receiver_state_change] UDPMessage: set Netsys_msg message to its request id {}", id);
              Some(Requests::Input_network (*id, name, msg))
            },
            // TODO it is unsound to using this active_fd
            None => {
              println!("[rs receiver_state_change] try to deliver Netsys_msg: contains no request id. set random id {}", active_fd);
              Some(Requests::Input_network ((active_fd as u64).into(), name, msg))
            },
          }
        })
      } else {
        eprintln!("[rs receiver_state_change] sender address unknown {}", addr);
        None
      }
    },
    Ok(Message(buf, _len)) => {
      print!("[rs receiver_state_change] Message fd {} socket_receive: (up to 30 chars) [", active_fd);
      for x in buf.clone().iter().take(30) {
        print!(" {:};", x);
      }
      println!("]");
      // sets current fd as active message id
      let id = active_fd as u64;
      let deser = Netsys_input::deserialise(&buf);
      // println!("[rs receiver_state_change] deser {:?}", deser);
      deser.and_then(|(msg,_len)| {
        // len == buf.len()
        Some(Requests::Input_direct (id.into(), adjust_id(msg, id.into())))
      })
    },
    Ok(NewClient(fd)) => {
      println!("[rs receiver_state_change] NewClient fd {} socket_receive new client {:?}", active_fd, fd);
      state.input_fds.push(fd);
      state.closed_fds.retain(|fd_| fd_ != &fd); // drop new client from list
      println!("[rs receiver_state_change] state.input_fds {:?}", state.input_fds);
      None
    },
    Err(e) => {
      eprintln!("[rs receiver_state_change] error socket_receive fd {} e: {:?}", active_fd, e);
      None
    }
  }
}

fn adjust_id(msg : Netsys_input, id : u64) -> Netsys_input {
  match msg {
    Netsys_input::Input_Ballot (sign, _rid, vote) => Netsys_input::Input_Ballot(sign,deserialise::Request_id::Request(id),vote),
    x => x,
  }
}

// TODO better suiting to implement try_into
fn request_id_id(x : &Request_id) -> &u64 {
  use crate::deserialise::Request_id::Request;
  let Request (id) = x;
  id
}

fn msg_id(x : &Netsys_msg ) -> Option<&u64> {
  match x {
    Netsys_msg::Msg_Ballot (_sign, rid, _vote) => Some (request_id_id(rid)),
    Netsys_msg::Msg_BallotRecorded (rid, _voter) => Some (request_id_id(rid)),
    Netsys_msg::Msg_BallotError (rid) => Some (request_id_id(rid)),
    Netsys_msg::Msg_Response(rid,_data) => Some(request_id_id(rid)),
    _ => None,
  }
}

fn lookup_addr(nodes : &[(Netsys_name,IpAddr,u16)], addr : String) -> Option<Netsys_name> {
  nodes.binary_search_by_key(&addr, |(_, ip, port)| format!("{ip}:{port}"))
                            .ok().map(|n| nodes[n].0)
}

fn lookup_name(nodes : &[(Netsys_name,IpAddr,u16)], name : &Netsys_name) -> Option<(IpAddr,u16)> {
  nodes.binary_search_by_key(name, |(nm, _, _)| *nm).ok()
    .map(|n| (nodes[n].1,nodes[n].2))
}

fn pad_msg(v : Vec<u8>) -> [u8; BUFFER_SIZE] {
  let mut buf = [0u8; BUFFER_SIZE];
  let min = std::cmp::min(v.len(),BUFFER_SIZE);
  buf[..min].copy_from_slice(&v[0..min]);
  buf
}

