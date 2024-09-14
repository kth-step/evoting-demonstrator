#![allow(unused_imports,dead_code,unused_variables)]

use std::os::raw::{c_int, c_uint};
use std::{thread, time};
use std::str;	//For from_utf8.
use std::env::args_os;

const BUFFER_LENGTH : usize = 38960;

#[link(name = "invoke_cakeml", kind = "static")]	//name = "invoke_cake" specifies the name of the library libinvoke_cakeml.a
extern "C" {
    fn invoke_cake(
		output_buffer: *const c_uint,
		output_buffer_size : c_uint,
		input_buffer: *const c_uint,
		input_buffer_size : c_uint) ->
		c_int;
}


fn act_upon_msg(input_buffer : &Vec<u8>, output_buffer : &mut Vec<u8>) {
    println!("rs: Increment message received.");
    for i in 0 .. BUFFER_LENGTH {
        output_buffer[i] = input_buffer[i].wrapping_add(1);
    }
}

fn buffer_to_ascii(buffer : &Vec<u8>) {
    print!("rs: buflen {}; bufstart:", buffer.len());
    for i in 0 .. std::cmp::min(30,buffer.len()) {
        print!(" {:x}", buffer[i]);
    }
    println!();
}

fn invoke_cakeml(output_buffer: &mut Vec<u8>, output_buffer_size: usize, input_buffer: &mut Vec<u8>, input_buffer_size: usize) -> i32 {
	let r = unsafe { invoke_cake(output_buffer.as_mut_ptr().cast(), output_buffer_size as u32, input_buffer.as_mut_ptr().cast(), input_buffer_size as u32) };
	return r;
}

fn main() {
	let mut input_buffer : Vec<u8> = vec![0; BUFFER_LENGTH];
    let mut output_buffer : Vec<u8> = vec![0; BUFFER_LENGTH];
    let input_buffer_size = BUFFER_LENGTH;
    let output_buffer_size = BUFFER_LENGTH;
    for i in 0..BUFFER_LENGTH {
        output_buffer[i] = i as u8;
    }
//	loop {
	for i in 0 .. 4 {
		let r = invoke_cakeml(&mut output_buffer, output_buffer_size, &mut input_buffer, input_buffer_size);
		buffer_to_ascii(&input_buffer);
		act_upon_msg(&input_buffer, &mut output_buffer);
    // artificial delay
    let one_sec = time::Duration::from_secs(2);
    thread::sleep(one_sec);
	}
}
