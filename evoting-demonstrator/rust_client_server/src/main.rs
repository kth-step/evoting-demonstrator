#![allow(unused_imports,unused_mut)]
use std::{
    fs,
    io::{prelude::*, BufReader},
    net::{TcpListener, TcpStream},
    thread,
    time::Duration,
};
use rust_client_server::ThreadPool;

use rust_app_lib::deserialise::*;
use rust_app_lib::deserialise::Netsys_msg::*;
use rust_app_lib::deserialise::Netsys_output::*;
use rust_app_lib::deserialise::Voter::*;
use deser_lib::Deserialise;
use deser_lib::Serialise;

use httparse;
use httparse::Status::Complete;

use serde_json::json;
use serde::{Deserialize, Serialize};

use base64::prelude::*;

#[derive(Debug, Deserialize)]
pub struct Vote {
  pub signature: String,
  pub vote: String,
}

use urlencoding::decode;

use std::os::unix::net::UnixStream;
const MAX_DATA_LENGTH : usize = 65_000;

fn main() {
    let address_default = "127.0.0.1:7878";

    let address = std::env::var("SERVER_ADDRESS").unwrap_or(address_default.into());

    println!("Starting server for client-input on http://{address}");
    let listener = TcpListener::bind(address).unwrap();
    let pool = ThreadPool::new(20);

    for stream in listener.incoming() {
        let stream = stream.unwrap();

        pool.execute(|| {
            handle_connection(stream);
        });
    }
    println!("Shutting down.");
}

fn handle_connection(mut stream: TcpStream) {
    const HEADER_LEN : usize = 100;
    let mut headers = [httparse::EMPTY_HEADER; HEADER_LEN];
    let mut req = httparse::Request::new(&mut headers);

    let mut buf_reader = BufReader::new(&mut stream);
    let buf = buf_reader.fill_buf().unwrap();
    let some_len = req.parse(buf);
    // println!("buf {:?}", buf);
    let len = buf.len();

    println!("\nnew request");
    println!("path {:?}", req.path);
    println!("method {:?}", req.method);
    println!("version {:?}", req.version);
    println!("headers {:?}", req.headers);

    let mut response : Option<&str> = None;
    let mut response_text : String;

    if let Ok(Complete(body_start)) = some_len {

        println!("body start: {:?}", body_start);
        println!("buf.len {:?}", len);
        let body = std::str::from_utf8(&buf[body_start..]).expect("input too short");
        // println!("{:?}", body);

        // look for ballot
        let needle = "ballot";
        // we assume no ampersand occurs in the data fields
        let parts = body.rsplit('&');
        for part in parts {
            if let Some((key,val)) = part.split_once('=') {
                // println!("{key}: {val}");
                if key == needle { // needle found

                    use core::cmp::min;
                    // strip length to consumable length
                    let data = val.split_at(min(val.len(),MAX_DATA_LENGTH)).0;
                    let decoded = decode(&data).expect("UTF-8").into_owned().replace("+"," ");
                    let vote : Result<Vote, serde_json::Error> = serde_json::from_str(&decoded).map(replace_in_vote);

                    if vote.is_err() {
                      println!("cannot parse vote json");
                      break;
                    }

                    let vote = vote.unwrap();
                    println!("Vote {:?}", vote);
                    // std::process::exit(9);

                    let sign = vote.signature.into_bytes();
                    // let enc_vote = BASE64_STANDARD.decode(vote.vote).expect("cannot base64 decode the vote");
                    let enc_vote = vote.vote.into();

                    let rid = Request_id::Request(0); // irrelevant
                    let data = Netsys_input::Input_Ballot(sign, rid, enc_vote).serialise().unwrap();

                    let data = sock_send_to( "/tmp/client.sock", &data);
                    print!("data (len 30 of total {:?}):\n[", data.len());
                    for x in data.iter().take(30) {
                        print!("{:}; ", x);
                    }
                    println!("]");

                    if let Some((Msg_Response(_rid,x),_len)) = <Netsys_msg>::deserialise(&data) {
                      let deser = <Netsys_output>::deserialise(&x);
                      if let Some((Output_BallotRecorded(_rid,Voter(voter_id)),_len)) = deser {
                        println!("deserialise response for id: {:?}", voter_id);
                        response_text = "OK ".to_owned() + &voter_id;
                        println!("answer message: {:?}", response_text);
                        response = Some(&response_text);
                      } else {
                        println!("cannot deserialise to Output_BallotRecorded");
                        println!("answer: {:?}", deser);
                      }
                    } else {
                        println!("cannot deserialise to Msg_Response");
                    }

                    break; // only process until first 'ballot' needle
                }
            }
        }
    }

    let data = request_data(response);
    stream.write_all(data.as_bytes()).unwrap();
}

// replaces spaces for + in the vote
fn replace_in_vote(vote : Vote) -> Vote {
  Vote {
    signature: vote.signature.replace(" ","+"),
    vote: vote.vote.replace(" ","+"),
  }
}

fn request_data(d: Option<&str>) -> String {
    let typ = "text/plain";
    let (status_line,length,contents) = match d {
        Some(x) => ("HTTP/1.1 200 OK", x.len(), x),
        None => ("HTTP/1.1 400 BAD REQUEST", 0, ""),
        // None => ("HTTP/1.1 404 NOT FOUND", 0, ""),
    };
    format!(
        "{status_line}\r\nContent-Length: {length}\r\nContent-Type: {typ}\r\n\r\n{contents}"
    )
}

fn sock_send_to(socket_address : &str, data : &Vec<u8>) -> [u8; MAX_DATA_LENGTH] {

  let mut stream = UnixStream::connect(socket_address).expect("Could not connect to socket");

  sock_write_request_and_shutdown(&mut stream, data);
  sock_read_from_stream(&mut stream)

}

fn sock_write_request_and_shutdown(stream: &mut UnixStream, data : &Vec<u8>) {

  stream
    .write_all(data)
    .expect("Failed writing to unix stream");

  println!("Shutting down writing on the stream, waiting for response...");
  stream
    .shutdown(std::net::Shutdown::Write)
    .expect("Could not shutdown writing on the stream");
  println!("after Shutdown::Write");
}

fn sock_read_from_stream(stream: &mut UnixStream) -> [u8; MAX_DATA_LENGTH] {
  //let mut response = String::new();
  let mut data = [0; MAX_DATA_LENGTH];
  stream
    //.read_to_string(&mut response)
    .read(&mut data)
    .expect("Failed at reading the unix stream");

  data
}

