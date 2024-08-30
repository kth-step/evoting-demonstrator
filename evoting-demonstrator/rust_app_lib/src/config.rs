#[cfg(feature = "emulation")]
use clap::Parser;

#[cfg(feature = "emulation")]
use std::error::Error;

use std::net::IpAddr;
use std::path::PathBuf;

use crate::deserialise::Netsys_name;

//  primary --node primary:127.0.0.1:8080 \
//  --node backup:127.0.0.1:8081 \
//  --socket /tmp/primary.sock \
//  --verbose --verbose

#[cfg(feature = "emulation")]
#[derive(Parser, Debug)]
#[command(version, about, long_about = None,)]
pub struct Config {
    /// the identifier of this node
    pub id: Netsys_name,

    /// nodes of shape `<identifier>:<ip>:<port>`
    #[arg(name="node", short, long, value_parser = parse_key_val_val::<Netsys_name,IpAddr,u16>)]
    pub nodes: Vec<(Netsys_name,IpAddr,u16)>,

    /// Sets a custom config file
    #[arg(short, long, value_name = "FILE")]
    pub socket: Option<PathBuf>,

    /// Turn debugging information on
    #[arg(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,

    // only used for pipes in emulation
	#[arg(trailing_var_arg(true))]
    pub pipes: Vec<String>,
}

#[cfg(not(feature = "emulation"))]
pub struct Config {
    pub id: Netsys_name,
    pub nodes: Vec<(Netsys_name,IpAddr,u16)>,
    pub socket: Option<PathBuf>,
    pub verbose: u8,
}

/// Parse a single key-value-value pair
#[cfg(feature = "emulation")]
fn parse_key_val_val<T, U, V>(s: &str) -> Result<(T, U, V), Box<dyn Error + Send + Sync + 'static>>
where
    T: std::str::FromStr,
    T::Err: Error + Send + Sync + 'static,
    U: std::str::FromStr,
    U::Err: Error + Send + Sync + 'static,
    V: std::str::FromStr,
    V::Err: Error + Send + Sync + 'static,
{
    let subs : Vec<_> = s.splitn(3,':').collect();
    Ok((subs[0].parse()?, subs[1].parse()?, subs[2].parse()?))
}

#[cfg(feature = "emulation")]
pub fn parse() -> Config {
    Config::parse()
}

#[test]
fn test_parse_key_val_val() {
  use std::net::Ipv4Addr;
  assert_eq!( (String::from("backup"), IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8081 as u16,),
    parse_key_val_val::<String,IpAddr,u16>("backup:127.0.0.1:8081").unwrap());
}

