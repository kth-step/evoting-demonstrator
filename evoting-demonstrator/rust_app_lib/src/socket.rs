extern crate libc;
use crate::select;
use std::path::PathBuf;

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

use std::{
    fs,
    io::prelude::*,
    net::{Shutdown, SocketAddr, UdpSocket},
    os::unix::{
        io::{AsRawFd, RawFd},
        net::{UnixListener, UnixStream},
    },
    time,
};

// #[cfg(debug_assertions)]
// pub const MAXMSGSIZE : usize = 20;

//#[cfg(not(debug_assertions))]
pub const MAXMSGSIZE: usize = 38960;
// >= 65508 fails with Os { code: 90, kind: Uncategorized, message: "Message too long" }

#[derive(Debug)]
pub enum Kind {
    Listener(UnixListener),
    Stream(UnixStream),
    UDPListener(UdpSocket),
}

#[derive(Debug)]
pub enum Receive {
    MarkShutdown,                     // socket disconnected
    Message([u8; MAXMSGSIZE], usize), // message received
    NewClient(RawFd),                 // new file descriptor
    UDPMessage([u8; MAXMSGSIZE], usize, SocketAddr), // udp message received
}

/// Creates a new unix listener socket and
/// adds it to the file descriptor hashmap `fd_map`.
pub fn socket_create(
    fd_map: &mut std::collections::HashMap<RawFd, Kind>,
    name: &PathBuf,
) -> Result<RawFd, String> {
    // errorcode:w2  fd:w2
    let socket_file = &name;
    // remove socket if exists
    let _ = fs::remove_file(socket_file);
    let mess = &format!(
        "rs socket_create: failed to create socket file {}",
        &socket_file.display()
    );
    let stream = UnixListener::bind(socket_file).expect(mess);
    let raw_fd = stream.as_raw_fd();
    stream
        .set_nonblocking(true)
        .expect("Couldn't set non-blocking");
    fd_map.insert(raw_fd, Kind::Listener(stream));
    log!(
        "[rs socket_create] socket at file {} for fd {:?}",
        &socket_file.display(),
        raw_fd
    );
    Ok(raw_fd)
}

/// Creates a new udp socket and
/// adds it to the file descriptor hashmap `fd_map`.
pub fn socket_create_udp(
    fd_map: &mut std::collections::HashMap<RawFd, Kind>,
    name: String,
) -> Result<RawFd, String> {
    // errorcode:w2  fd:w2
    // remove socket if exists
    let mess = &format!("rs socket_create_udp: failed to bind to {}", &name);
    let socket = UdpSocket::bind(&name).expect(mess);
    socket
        .set_read_timeout(Some(time::Duration::new(1, 0)))
        .expect("Couldn't set read timeout");
    let raw_fd = socket.as_raw_fd();

    fd_map.insert(raw_fd, Kind::UDPListener(socket));
    log!(
        "[rs socket_create_udp] socket name {} for fd {:?}",
        name,
        raw_fd
    );
    Ok(raw_fd)
}

pub fn socket_receive(
    fd_map: &mut std::collections::HashMap<RawFd, Kind>,
    fd: RawFd,
) -> Result<Receive, String> {
    // errorcode :w2  msg:word8array
    match fd_map.get_mut(&fd) {
        None =>
            Err(format!("rs socket_receive: connection for fd {} unknown", fd)),
        // receive content
        Some(Kind::Stream(stream)) => {
          // should read and return the message
          let mut response : [u8; MAXMSGSIZE] = [0; MAXMSGSIZE];
          stream.set_read_timeout(Some(time::Duration::new(1, 0))).expect("Couldn't set read timeout");

          let size = stream.read(&mut response);
          match size {
            Ok(len) if len == 0 => {
                // client disconnects
                log!("[rs socket_receive] Kind::Stream: mark shutdown client writer fd {}", fd);
                // mark for shutdown
                Ok(Receive::MarkShutdown)
            }
            Ok(len) => {
                log!("[rs socket_receive] Kind::Stream: fd {} len {}: {:?}", fd, len, &response[0..std::cmp::min(20,len)]);
                Ok(Receive::Message(response, len))
            },
            Err(e) =>
                Err(format!("rs socket_receive Kind::Stream: unkown error reading from stream fd {} {:?}", fd, e)),
          }
        },
        // receive connection
        Some(Kind::Listener(listener)) => match listener.accept() {
            Ok((conn, _addr)) => {
                log!("[rs socket_receive] Kind::Listener: new client conn: {:?}", conn);
                conn.set_nonblocking(true).expect("Couldn't set non-blocking");
                let fd = conn.as_raw_fd();
                fd_map.insert(fd, Kind::Stream(conn));
                Ok(Receive::NewClient((fd as u32).try_into().unwrap()))
            },
            Err(e) =>
                Err(format!("rs socket_receive Kind::Listener: unkown error receiving client from listener fd {} {:?}", fd, e)),
        },
        // receive UDP connection
        Some(Kind::UDPListener(socket)) => {
            log!("[rs socket_receive] Kind::UDPListener: {:?}", socket);
            // should read and return the message
            let mut response : [u8; MAXMSGSIZE] = [0; MAXMSGSIZE];
            match socket.recv_from(&mut response) {
                Ok((len, addr)) => {
                    log!("[rs socket_receive] Kind::UDPListener fd {} len {} from {:?}; {:?}", fd, len, addr, &response[0..std::cmp::min(20,len)]);
                    Ok(Receive::UDPMessage(response, len, addr))
                },
                Err(e) =>
                    Err(format!("rs socket_receive Kind::UDPListener: unkown error reading from UDP fd {} {:?}", fd, e)),
            }
        }
    } // match val
}

pub fn socket_send(
    fd_map: &mut std::collections::HashMap<RawFd, Kind>,
    fd: RawFd,
    msg: &[u8; MAXMSGSIZE],
) -> Result<(), String> {
    let len = msg.len();
    log!(
        "[rs socket_send] sending to {} msg[0..20]: {:?}",
        fd,
        &msg[0..std::cmp::min(20, len)]
    );
    match fd_map.get_mut(&fd) {
        None => {
            log!("[rs socket_send] fd not found in hashmap");
            Err(format!("[rs socket_send] connection for fd {} unknown", fd))
        },
        Some(Kind::Stream(conn)) => {
          log!("[rs socket_send] Kind::Stream");
          if let Ok(Some(err)) = conn.take_error() {
              log!("[rs socket_send] stream error {err:?}");
              return Err(format!("[rs socket_send] stream error {err:?}"))
          }
          match conn.write(msg) {
              Ok(len) => if len < msg.len() {
                      Err(format!("[rs socket_send] wrote {} of {} byte(s)", len, msg.len()))
                  } else {
                    Ok(())
                  },
              Err(e) => {
                  log!("[rs socket_send] stream write error {e:?}");
                  Err(format!("[rs socket_send] stream write error {e:?}"))
              }
          }
          //conn
          //    .write_all(msg)
          //    .map_err(|e| format!("[rs socket_send] unknown error writing to fd {} {:?}", fd, e))
        },
        Some(Kind::Listener(_)) => {
            log!("[rs socket_send] error writing to listener fd {}", fd);
            Err(format!(
            "[rs socket_send] error writing to listener fd {}",
            fd
        ))
        },
        Some(Kind::UDPListener(_)) => {
            log!("[rs socket_send] error writing to UDP listener fd {}", fd);
            Err(format!(
            "[rs socket_send] error writing to UDP listener fd {} using non udp send",
            fd
        ))
        },
    }
}

pub fn socket_send_udp(
    fd_map: &mut std::collections::HashMap<RawFd, Kind>,
    fd: RawFd,
    addr: SocketAddr,
    msg: &[u8; MAXMSGSIZE],
) -> Result<(), String> {
    log!(
        "[rs socket_send_udp] sending to addr {:?} at fs {} msg {:?}",
        addr,
        fd,
        &msg[..MAXMSGSIZE.min(20)]
    );
    match fd_map.get_mut(&fd) {
        None => Err(format!(
            "[rs socket_send_udp] connection for fd {} unknown",
            fd
        )),
        Some(Kind::UDPListener(socket)) => {
            match socket.send_to(msg, addr) {
                Ok(len) => log!(
                    "[rs socket_send_udp] sent {} bytes to addr {} over fd {}",
                    len,
                    addr,
                    fd
                ),
                Err(e) => log!(
                    "[rs socket_send_udp] send to addr {} failed with {:?}",
                    addr,
                    e
                ),
            }
            Ok(())
        }
        Some(_) => Err(format!("rs socket_send_udp: no UDP socket at fd {}", fd)),
    }
}

pub fn socket_close(
    fd_map: &mut std::collections::HashMap<RawFd, Kind>,
    fd: RawFd,
) -> Result<(), String> {
    match fd_map.remove(&fd) {
        None => return Err(format!("rs socket_close: connection for fd {} unknown", fd)),
        Some(Kind::Stream(conn)) => {
            let _ = conn.shutdown(Shutdown::Both);
        }
        Some(Kind::Listener(_listener)) => {}
        Some(Kind::UDPListener(_)) => {}
    }
    Ok(())
}

pub fn select(
    fd_map: &mut std::collections::HashMap<RawFd, Kind>,
    fds: &[RawFd],
) -> Result<Vec<RawFd>, String> {
    if fds.is_empty() {
        return Ok([].to_vec());
    }
    if fd_map.is_empty() {
        return Err(format!(
            "rs select: trying to select {:?} from {} connections",
            fds,
            fd_map.len()
        ));
    }
    // gets the maximal file descriptor
    let (max_fd, _) = &fd_map
        .iter()
        .max_by(|(a, _v), (b, _w)| a.partial_cmp(b).unwrap())
        .unwrap();

    // prepares the set of file descriptors for FdSet
    let mut fd_set = select::FdSet::new();
    for fd in fds {
        if fd_map.contains_key(fd) {
            fd_set.set(*fd);
        }
    }

    let mut new_fds = vec![];
    let timeout = time::Duration::new(10, 0);
    match select::pselect(
        *max_fd + 1,
        Some(&mut fd_set), // read
        None,              // write
        None,              // error
        Some(timeout),     // timeout
        None,              // mask
    ) {
        // no activity
        Ok(num) if num == 0 => new_fds = [].to_vec(),
        Err(e) => {
            return Err(format!("rs select: failed to select: {:?}", e));
        }
        // no of active file descriptors
        Ok(num) => {
            log!("[rs select] number of active fds {}", num);

            for fd in fds {
                if (fd_set).is_set(*fd) {
                    new_fds.push(*fd);
                    log!("[rs select] active fd {:?}", fd);
                }
            }
        }
    }
    Ok(new_fds)
}
