#![allow(clippy::enum_variant_names)]
#![allow(non_camel_case_types, unused_macros)]

use deser_lib::{Deserialise, Serialise};
/// Serialises and deserialises the datatypes from
/// the networked voting server
use deser_macro::{Deserialise, Serialise};

use std::str::FromStr;

/// Parts of the data transferred from CakeML/HOL4 needs to be deserialised
/// into rust data structures.

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

// ../../src/formatScript.sml
// PartialEq for testing
#[derive(Debug, Serialise, Deserialise, Clone, PartialEq)]
pub enum Request_id {
  Request(u64),
}

#[derive(Debug, Serialise, Deserialise, Clone, PartialEq)]
pub enum Voter {
  Voter(String),
}

// ../../src/tevd/hol/TevDNetworkedSystemScript.sml
#[derive(Default, Debug, Serialise, Deserialise, Clone, PartialEq, Ord, Eq, PartialOrd, Copy)]
pub enum Netsys_name {
  #[default]
  Name_VCS,
  Name_MixNet,
  Name_Admin,
  Name_Client,
}

#[derive(Debug, Serialise, Deserialise, Clone, PartialEq)]
pub enum Netsys_msg {
  Msg_VotingStart(Vec<Voter>),
  Msg_VotingEnd,
  Msg_Ballot(Vec<u8>, Request_id, Vec<u8>), // signature@0 vote@2
  Msg_BallotRecorded(Request_id, Voter),
  Msg_BallotError(Request_id),
  Msg_Ballots(Vec<u8>),
  Msg_Response(Request_id, Vec<u8>),
  Msg_Confirm,
}

#[derive(Debug, Serialise, Deserialise, Clone, PartialEq)]
pub enum Netsys_input {
  // signature@0 vote@2
  Input_Ballot(Vec<u8>, Request_id, Vec<u8>),
  Input_VotingStart(Vec<Voter>),
  Input_VotingEnd,
}

#[derive(Debug, Serialise, Deserialise, Clone)]
pub enum Netsys_output {
  Output_Ballots(Vec<u8>),
  Output_BallotRecorded(Request_id, Voter),
  Output_BallotError(Request_id),
  Confirm,
}

// ../../src/tevd/hol/TevDNetworkedSystemScript.sml
#[derive(Debug, Serialise, Deserialise, Clone, PartialEq)]
pub enum Response {
  Response(u64, Vec<(Netsys_name, Netsys_msg)>),
  DeserialiseFail,
}

#[derive(Debug, Serialise, Deserialise, Clone)]
pub enum Requests {
  Input_direct(u64, Netsys_input),
  Input_network(u64, Netsys_name, Netsys_msg),
}

#[derive(Debug, PartialEq, Eq)]
pub struct ParseNetsysNameError;

impl std::error::Error for ParseNetsysNameError {}
impl std::fmt::Display for ParseNetsysNameError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "Cannot parse name")
  }
}

impl FromStr for Netsys_name {
  type Err = ParseNetsysNameError;
  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s.to_lowercase().as_str() {
      "vcs" => Ok(Netsys_name::Name_VCS),
      "mixnet" => Ok(Netsys_name::Name_MixNet),
      "admin" => Ok(Netsys_name::Name_Admin),
      "client" => Ok(Netsys_name::Name_Client),
      s => {
        if let Some(s) = s.strip_prefix("name_") {
          Self::from_str(s)
        } else {
          Err(ParseNetsysNameError)
        }
      }
    }
  }
}

impl ToString for Netsys_name {
  fn to_string(&self) -> String {
    match self {
      Netsys_name::Name_VCS => "vcs".to_string(),
      Netsys_name::Name_MixNet => "mixnet".to_string(),
      Netsys_name::Name_Admin => "admin".to_string(),
      Netsys_name::Name_Client => "client".to_string(),
    }
  }
}

#[cfg(test)]
mod tests {
  // importing names from outer scope
  use super::*;

  // copy of tests from HOL4:
  // ../../src/tevd/hol/selftest.sml
  #[test]
  fn test_ser() {
    assert_eq!(Netsys_name::Name_VCS.serialise(), Some(vec![0u8]));
    assert_eq!(Netsys_name::Name_MixNet.serialise(), Some(vec![1u8]));
    let resp = Response::Response(
      42,
      vec![(
        Netsys_name::Name_MixNet,
        Netsys_msg::Msg_VotingStart(vec![]),
      )],
    );
    assert_eq!(
      resp.serialise(),
      Some(vec![0u8, 0, 0, 0, 0, 0, 0, 0, 42, 1, 1, 0, 0])
    );
    let resp = Response::Response(
      42,
      vec![(
        Netsys_name::Name_MixNet,
        Netsys_msg::Msg_BallotRecorded(
          Request_id::Request(2001),
          Voter::Voter(String::from("abc")),
        ),
      )],
    );
    assert_eq!(
      resp.serialise(),
      Some(vec![
        0u8, 0, 0, 0, 0, 0, 0, 0, 42, 1, 1, 3, 0, 0, 0, 0, 0, 0, 0, 7, 209, 0, 3, 97, 98, 99
      ])
    );
    let inp = Requests::Input_network(380, Netsys_name::Name_MixNet, Netsys_msg::Msg_Confirm);
    assert_eq!(
      inp.serialise(),
      Some(vec![1u8, 0, 0, 0, 0, 0, 0, 1, 124, 1, 7])
    );
  }

  #[test]
  fn test_req_zero() {
    let deser = Request_id::Request(0u64);
    let ser = vec![0u8, 0, 0, 0, 0, 0, 0, 0, 0];
    assert_eq!(Some(ser.clone()), deser.clone().serialise());
    assert_eq!(<Request_id>::deserialise(&ser), Some((deser, ser.len())));
  }

  #[test]
  fn test_netsys_msg() {
    let deser = Netsys_msg::Msg_Ballot(vec![], Request_id::Request(0u64), vec![]);
    let ser = vec![2u8, 0, 0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    assert_eq!(Some(ser.clone()), deser.clone().serialise());
    assert_eq!(<Netsys_msg>::deserialise(&ser), Some((deser, ser.len())));
    /*
      EVAL o Term $ `serialise_netsys_msg $ Msg_Ballot [] (Request 0w) []`
      ⊢ serialise_netsys_msg (Msg_Ballot [] (Request 0w) []) =
        SOME [2w; 0w;  0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w]: thm
    */
  }

  #[test]
  fn test_netsys_input() {
    let deser = Netsys_input::Input_Ballot(vec![1u8], Request_id::Request(1u64), vec![0u8]);
    let ser = vec![0, 1, 1, 0u8, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0];
    assert_eq!(Some(ser.clone()), deser.clone().serialise());
    assert_eq!(<Netsys_input>::deserialise(&ser), Some((deser, ser.len())));
    /*
      serialise_netsys_input (Input_Ballot [1w] (Request 1w) [0w])
        = SOME [0w;   1w; 1w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 1w; 1w; 0w]
      Input_Ballot [1w]      (Request   1w)                              [0w]
      [0w;         1w; 1w;   0w;        0w; 0w; 0w; 0w; 0w; 0w; 0w; 1w;   1w; 0w]
    */
  }

  #[test]
  fn test_parse_netsys_name() {
    assert_eq!(Netsys_name::from_str("vcs").unwrap(), Netsys_name::Name_VCS);
    assert_eq!(
      "mixnet".parse::<Netsys_name>().unwrap(),
      Netsys_name::Name_MixNet
    );
    assert!("invalid".parse::<Netsys_name>().is_err());
  }

  #[test]
  fn test_parse_netsys_response() {
    assert_eq!(Netsys_name::from_str("vcs").unwrap(), Netsys_name::Name_VCS);
    let ser = vec![
      0u8, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0,
    ];
    let deser = <Response>::deserialise(&ser);
    assert_eq!(
      deser,
      Some((
        Response::Response(
          0,
          [(
            Netsys_name::Name_VCS,
            Netsys_msg::Msg_Ballot([1].to_vec(), Request_id::Request(1), [0].to_vec())
          )]
          .to_vec()
        ),
        25
      ))
    );
  }
} // mod test
