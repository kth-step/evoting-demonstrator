use crate::deserialise::Netsys_name;
use std::{env::Args, net::IpAddr, path::PathBuf, str::FromStr};

pub fn parse(
  args: &mut Args,
  state: &mut Vec<(Netsys_name, IpAddr, u16)>,
  id: &mut Netsys_name,
  debug_cnt: &mut usize,
  path: &mut Option<PathBuf>,
) -> bool {
  let _prg_name = args.next();
  while let Some(arg) = args.next() {
    match &arg[..] {
      "--node" => {
        let Some(arg) = args.next() else { return false };
        let y = arg.split(":").collect::<Vec<_>>();
        if y.len() != 3 {
          println!("[parse rs] y has length {}", y.len());
          return false;
        }
        let name = Netsys_name::from_str(y[0]).unwrap();
        let ip: IpAddr = y[1].parse().unwrap();
        let port: u16 = y[2].parse().unwrap();
        state.push((name, ip, port));
        println!("[rs parse] node definition {:?}", y);
      }
      "--socket" => {
        let Some(arg) = args.next() else { return false };
        *path = Some(PathBuf::from(arg));
      }
      "-v" => {
        *debug_cnt += 1;
      }
      name if Netsys_name::from_str(&name).is_ok() => {
        *id = Netsys_name::from_str(&name).unwrap();
        println!("[rs parse] node name: {:?}", id);
      }
      _ => return false,
    }
  }
  true
}
