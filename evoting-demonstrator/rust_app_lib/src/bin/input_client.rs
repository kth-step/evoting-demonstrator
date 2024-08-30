use rust_app_lib::deserialise::*;
use rust_app_lib::deserialise::Netsys_msg::*;
use deser_lib::Deserialise;
use deser_lib::Serialise;
use std::{
  io::{Read, Write},
  os::unix::net::UnixStream,
};

const BUFFER_LENGTH : usize = 38960;

fn main() {

  let sign = vec![1];
  let enc_vote = vec![0];
  let ballot = Netsys_input::Input_Ballot(sign, Request_id::Request(1), enc_vote);
  // let ballot = Netsys_msg::Msg_Ballot(sign, Request_id::Request(1), enc_vote);
  println!("{ballot:?}");
  let data = ballot.serialise().expect("could not deserialise ballot");
  println!("{:?}", data);

  let socket = "/tmp/client.sock";
  let mut stream = UnixStream::connect(socket).expect("Could not connect to socket");

  //let filename = "test_assets/signed_vote.json";
  //let data = fs::read(filename).expect("Could not read jws file");

  write_request_and_shutdown(&mut stream, data);
  read_from_stream(&mut stream);
}

fn write_request_and_shutdown(stream: &mut UnixStream, data : Vec<u8>) {

  stream
    .write_all(&data)
    .expect("Failed writing to unix stream");

  println!("Shutting down writing on the stream, waiting for response...");
  stream
    .shutdown(std::net::Shutdown::Write)
    .expect("Could not shutdown writing on the stream");
}

fn read_from_stream(stream: &mut UnixStream) {
  //let mut response = String::new();
  let mut data = [0; BUFFER_LENGTH];
  stream
    //.read_to_string(&mut response)
    .read(&mut data)
    .expect("Failed at reading the unix stream");

  print!("data (len 30 of total {:?}):\n[", data.len());
  for x in data.iter().take(30) {
    print!("{:}; ", x);
  }
  println!("]");

  if let Some((Msg_Response(_id,a),_)) = <Netsys_msg>::deserialise(&data) {
    let x = <Netsys_output>::deserialise(&a);
    println!("deserialise response: {:?}", x);
  } else {
    println!("cannot deserialise response");
  }
}

