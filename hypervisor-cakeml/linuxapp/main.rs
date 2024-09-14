#![allow(unused_imports,dead_code,unused_variables)]
#![feature(c_size_t)]

use std::env;
use std::os::raw::{c_int, c_char, c_void};
use core::ffi::c_size_t;
use std::{thread, time};
use std::cmp::min;

const BUFFER_SIZE : usize = 12;

#[derive(Debug)]
struct Config<'a> {
    id    : &'a str,
    nodes : Vec<&'a str>,
    exec  : &'a str,
}

// name = libhypercall
#[link(name = "hypercall")]
extern "C" {
    fn hypercall(ptr_in : *const c_char, len_in : *const c_size_t, ptr_out : *mut c_char, len_out : *mut c_size_t,) -> c_void;
}

enum MessageType {
    SendMsg,
    GetSelf,
    Undefined,
}

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

fn num_to_message_type (n : u8) -> MessageType {
    match n {
        2 => MessageType::SendMsg,
        1 => MessageType::GetSelf,
        _ => MessageType::Undefined,
    }
}

/// buf_in[BUFFER_SIZE]  = type : u8, len : vec[u8; 2], data
/// buf_out[BUFFER_SIZE] = type : u8, len : vec[u8; 2], data
fn act_upon_msg(buf_in : &Vec<u8>, buf_out: &mut Vec<u8>, c : &Config) {
    if buf_in.len() == 0 || buf_out.len() == 0 {
        println!("rs error with buffer length");
        return;
    }
    match num_to_message_type(buf_in[0]) {
        MessageType::SendMsg => {
            todo!();
        },
        MessageType::GetSelf => {
            let id : Vec<u8> = c.id.as_bytes().to_vec();
            let len = min(buf_out.len()-3,id.len());
            buf_out[0] = 1;
            int_to_byte2_offset(len as i16, buf_out, 1);
            for i in 0..len {
                buf_out[i+3] = id[i];
            }
        },
        MessageType::Undefined => {
            // empty msg
            let len = buf_out.len();
            for x in 0..len {
                buf_out[x] = 0;
            }
        },
    }
}


fn main() {
    let mut args : Vec<String> = env::args().collect();
    let id = args.pop().unwrap();
    let exec = args.pop().unwrap();
    let c = Config {id : id.as_str(), nodes: vec![], exec : exec.as_str() };

    println!("rs c: {:?}", c);
    println!("rs c.exec: {:?}", c.exec);

    let mut buf_in : Vec<u8> = vec![0; BUFFER_SIZE];
    let mut buf_out : Vec<u8> = vec![0; BUFFER_SIZE];
    let mut len_out = BUFFER_SIZE;
    let mut len_in = BUFFER_SIZE;

    loop {
        println!("rs hypercall(buf_in[{}]) = buf_out[{}]", len_in, len_out);
        println!("rs buf_in[{}]: {:?}", len_in, buf_in);
        unsafe {
            assert!(len_in <= BUFFER_SIZE);
            // hypercall(buf_in) = buf_out
            hypercall(buf_in.as_mut_ptr().cast(), &len_in, buf_out.as_mut_ptr().cast(), &mut len_out);
            assert!(len_out <= BUFFER_SIZE);
        }
        println!("rs buf_out[{}]: {:?}", len_out, buf_out);
        // act_upon_msg(buf_out) = buf_in
        act_upon_msg(&buf_out, &mut buf_in, &c);
        len_out = BUFFER_SIZE;
        len_in = BUFFER_SIZE;
        // artificial delay
        let one_sec = time::Duration::from_secs(1);
        thread::sleep(one_sec);
        println!("");
    }
}

