
use std::io::{Read, Write};
use std::net::UdpSocket;
use std::net::{TcpListener, TcpStream, Shutdown};
use std::sync::{Mutex,Arc};
use std::thread;

/*
 * The TCP server is a simple server that echos the data received over UDP,
 * which is stored in the buffer shared_data
 */

const UDP_BUF_SIZE : usize = 4096; // incoming
const TCP_BUF_SIZE : usize = 8192; // outgoing

fn main() {
    let udp_listen_default : &str = "127.0.0.1:7878";
    let udp_address = std::env::var("UDP_ADDRESS").unwrap_or(udp_listen_default.into());

    // shared data received over UDP
    let shared_data = Arc::new(Mutex::new(([0u8; UDP_BUF_SIZE], 0usize)));

    {
        let shared_data_tcp = Arc::clone(&shared_data);
        thread::spawn(move|| init_tcp_server(&shared_data_tcp));
/*
        thread::spawn(move || 
            loop {
                output_debug(&shared_data_tcp);
                std::thread::sleep(std::time::Duration::from_millis(1000));
            }
        );
*/
    }

    // handle UDP receival
    // let mut buf = [0u8; UDP_BUF_SIZE];
    match UdpSocket::bind(udp_address.clone()) {
        Ok(socket) => {
            println!("UDP echo Server is listening on {}", udp_address);
            let mut error_number = 0;
            loop {
                let shared_data_udp = Arc::clone(&shared_data);
                let mut buffer = [0u8; UDP_BUF_SIZE];
                match socket.recv_from(&mut buffer) {
                    Ok((n, addr)) => {
                        println!("UDP receive {} bytes from {:?}: {:?}", n, addr.to_string(), &buffer[0..n]);
                        let mut shared_data_ref = shared_data_udp.lock().unwrap();
                        *shared_data_ref = (buffer, n);
/*
                        match socket.send_to(&buf[0..n], addr) {
                            Ok(_) => {}
                            Err(e) => println!("Send to {} error: {:?}", addr.to_string(), e),
                        }
                        error_number = 0;
*/
                    }
                    Err(e) => {
                        error_number += 1;
                        println!("UDP receive from {} error #{}: {:?}", udp_address, error_number, e);
                        if error_number >= 10 {
                            break;
                        }
                        // sleep(Duration::from_millis(2u64.pow(error_number as u32))); // 2 ^ 9 = 512 ms
                    }
                }
            }
        }
        Err(e) => println!("UDP bind to {} error: {:?}", udp_address, e),
    }
    // sleep(Duration::from_secs(1));
}

fn handle_tcp_client(mut stream: TcpStream, shared_data : Arc<Mutex<([u8; UDP_BUF_SIZE], usize)>> ) {
                     //, buffer : &[u8; UDP_BUF_SIZE], buflen : usize) {
    let mut data = [0 as u8; TCP_BUF_SIZE]; // using 50 byte buffer

    'stream_read: while match stream.read(&mut data) {
        Ok(size) => {
            let shared_data = shared_data.lock().unwrap();
            // write everything
            println!("TCP receive {} bytes of data", size);
            let buf_size = UDP_BUF_SIZE;
            let buffer = shared_data.0;

            // debug buffer content
            let min_len = core::cmp::min(30,buf_size);
            print!("buffer (len 30 of total {:?}):\n[", min_len);
            for x in buffer.iter().take(min_len) {
                print!("{:}; ", x);
            }
            println!("]");

            let answer = request_data(&buffer[0..buf_size]);
            // *shared_data = (buffer, buf_size);

            let r = stream.write_all(&answer);
            if r.is_ok() {
                println!("TCP successful answer");
                let _ = stream.shutdown(Shutdown::Both);
            } else {
                println!("TCP unsuccessful answer (maybe stream shutdown)");
                break 'stream_read;
            }
            true
        },
        Err(e) => {
            println!("An error occurred, terminating connection with {}", stream.peer_addr().unwrap());
            println!("error {}", e);
            let _ = stream.shutdown(Shutdown::Both);
            false
        }
    } {}
    let _ = stream.shutdown(Shutdown::Both);
    stream.flush().unwrap();
}

#[allow(dead_code)]
fn output_debug (shared_data : &Arc<Mutex<([u8; UDP_BUF_SIZE], usize)>>) {
    let shared_data_ref = shared_data.lock().unwrap();
    let (buffer,buf_size) = *shared_data_ref;
    let min_len = core::cmp::min(30,buf_size);
    print!("buffer (len 30 of total {:?}):\n[", min_len);
    for x in buffer.iter().take(min_len) {
        print!("{:}; ", x);
    }
    println!("]");
}

fn init_tcp_server(shared_data : &Arc<Mutex<([u8; UDP_BUF_SIZE], usize)>>) {
    let tcp_listen_default : &str = "127.0.0.1:7879";
    let tcp_address = std::env::var("TCP_ADDRESS").unwrap_or(tcp_listen_default.into());
    println!("Server listening on {}", tcp_address);
    let listener = TcpListener::bind(tcp_address).unwrap();
    // accept connections and process them, spawning a new thread for each one
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                println!("New connection: {}", stream.peer_addr().unwrap());
                let shared_data = Arc::clone(shared_data);
                thread::spawn(move|| {
                    // connection succeeded
                    handle_tcp_client(stream, shared_data)
                });
            }
            Err(e) => {
                println!("Error: {}", e);
                /* connection failed */
            }
        }
    }
    // close the socket server
    // drop(listener);
}

fn request_data(d: &[u8]) -> Vec<u8> {
    let typ = "text/plain";
    let (status_line,length) = if 0 < d.len() 
    {
        ("HTTP/1.1 200 OK", d.len())
    } else {
        ("HTTP/1.1 400 BAD REQUEST", 0)
    };
    let mut header = format!(
        "{status_line}\r\nContent-Length: {length}\r\nContent-Type: {typ}\r\n\r\n"
    ).into_bytes();
    header.extend_from_slice(d);
    header
}

