pub trait Serialise {
  fn serialise (self) -> Option<Vec<u8>>;
}

pub trait Deserialise {
  fn deserialise(_ : &[u8]) -> Option <(Self, usize)> where Self: Sized;
}

impl Serialise for u8 {
  // HOL4: serialise_word8
  fn serialise (self : u8) -> Option<Vec<u8>>{
    Some(vec![self])
  }
}

impl Deserialise for u8 {
  // HOL4: deserialise_word8
  fn deserialise(buf : &[u8]) -> Option <(u8, usize)> {
    if buf.is_empty() {
      None
    } else {
      Some((buf[0], 1))
    }
  }
}

// can be similarly implemented for any other number type
impl Serialise for u16 {
  // HOL4: serialise_word16
  fn serialise (self : u16) -> Option<Vec<u8>>{
    Some(self.to_be_bytes().to_vec())
  }
}

impl Deserialise for u16 {
  // HOL4: deserialise_word16
  fn deserialise(buf : &[u8]) -> Option <(u16, usize)> {
    if buf.len() < 2 { return None; }
    let (hd,_tl) = buf.split_at(2); // std::mem::size_of::<u16>()
    hd.try_into().ok().map(|u| (u16::from_be_bytes(u), 2))
  }
}

impl Serialise for u32 {
  // HOL4: serialise_word32
  fn serialise (self : u32) -> Option<Vec<u8>>{
    Some(self.to_be_bytes().to_vec())
  }
}

impl Deserialise for u32 {
  // HOL4: deserialise_word32
  fn deserialise(buf : &[u8]) -> Option <(u32, usize)> {
    if buf.len() < 4 { return None; }
    let (hd,_tl) = buf.split_at(4); // std::mem::size_of::<u32>()
    hd.try_into().ok().map(|u| (u32::from_be_bytes(u), 4))
  }
}

impl Serialise for u64 {
  // HOL4: serialise_word64
  fn serialise (self : u64) -> Option<Vec<u8>>{
    Some(self.to_be_bytes().to_vec())
  }
}

impl Deserialise for u64 {
  // HOL4: deserialise_word64
  fn deserialise(buf : &[u8]) -> Option <(u64, usize)> {
    if buf.len() < 8 { return None; }
    let (hd,_tl) = buf.split_at(8); // std::mem::size_of::<u64>()
    hd.try_into().ok().map(|u| (u64::from_be_bytes(u), 8))
  }
}

/*
impl<T> Serialise for Vec<T> where T : Serialise + std::clone::Clone {
  // HOL4: serialise_list
  fn serialise (self : Vec<T>) -> Option<Vec<u8>> {
    if self.is_empty() {
      return Some(vec![0])
    }
    let (hd,tl) = self.split_at(1);
    let hd = &hd[0];
    match hd.clone().serialise() {
      None => None,
      Some(elem) =>
        match Vec::<T>::serialise(tl.to_vec()) {
          None => None,
          Some (buf) => {
            let hd = vec![1];
            Some([hd,elem,buf].concat())
          },
        },
    }
  }
}
*/

impl<T> Serialise for Vec<T>
  where T : Serialise + std::clone::Clone
{
  // HOL4: serialise_long_list
  fn serialise (self : Vec<T>) -> Option<Vec<u8>> {
    let len = std::cmp::min (self.len(), 254);
    let (hds,tls) = self.split_at(len);
    let vec_opt = Some(vec![]);
    let hds_bytes = hds.iter().fold(vec_opt, |vec_opt, x| {
      vec_opt.and_then(|vec| x.clone().serialise().map(|x_bytes| [vec,x_bytes].concat()))
    });
    if tls.is_empty() {
      // len < 254
      hds_bytes.map(|x| {
          let mut v = Vec::with_capacity(1 + x.len());
          v.push(len as u8);
          v.extend(x);
          v
      })
    } else {
      hds_bytes.and_then(|hds_bytes|
        tls.to_vec().serialise().map(|tls_bytes| [vec![255u8], hds_bytes, tls_bytes].concat())
      )
    }
  }
}

impl<T> Deserialise for Vec<T>
  where T : Deserialise + Clone {
  // HOL4: deserialise_long_list
  fn deserialise(buf : &[u8]) -> Option <(Vec<T>, usize)> {
    let len = buf.len();
    if len == 0 { return None; }
    // first items
    let items = buf[0] as usize;
    // println!("first item: {}", items);
    let pre = {
      let mut ret = Vec::new();
      let mut pt_total = 1;
      let no_items = std::cmp::min (items, 254);
      for _ in 0..no_items {
        if len <= pt_total { return None }
        let Some ((t, pt_rest)) = T::deserialise(&buf[pt_total..]) else {
          return None
        };
        ret.push(t);
        // println!("pt_total {}, pt_rest {}", pt_total, pt_rest);
        pt_total += pt_rest;
      }
      // println!("len {}, pt_total {}, items {}", len, pt_total, items);
      Some ((ret, pt_total))
    };
    if items < 255 { return pre }
    match pre {
      None => None,
      Some((t, pt)) => {
        // pt = 255
        let rest = Self::deserialise(&buf[255..]);
        rest.map(|(t_r, pt_r)| ([t,t_r].concat(), pt + pt_r))
      }
    }
  }
}

impl<T,U> Serialise for (T,U)
  where T : Serialise, U : Serialise {
  // HOL4: serialise_pair
  fn serialise (self : (T,U)) -> Option<Vec<u8>> {
    match T::serialise(self.0) {
      None => None,
      Some (fst) =>
        match U::serialise(self.1) {
          None => None,
          Some (snd) => {
              let mut v = Vec::with_capacity(fst.len() + snd.len());
              v.extend(fst);
              v.extend(snd);
              Some (v)
          }
        }
    }
  }
}

impl<T,U> Deserialise for (T,U)
  where
  T : Deserialise, U : Deserialise {
  // HOL4: deserialise_pair
  fn deserialise(buf : &[u8]) -> Option <((T,U), usize)> {
    match T::deserialise(buf) {
      None => None,
      Some ((t,pt)) =>
        U::deserialise(&buf[pt..]).map(|(u,pt2)| ((t,u),pt+pt2))
    }
  }
}

impl Serialise for String {
  // HOL4: serialise_string
  fn serialise (self : String) -> Option<Vec<u8>>{
    let len = self.len();
    if len == 0 || 256 < len { return None }
    let mut ret = vec![len as u8];
    ret.append(&mut self.into_bytes());
    Some(ret)
  }
}

impl Deserialise for String {
  // HOL4: deserialise_string
  fn deserialise(buf : &[u8]) -> Option <(String, usize)> {
    if buf.is_empty() { return None }
    let len = buf[0] as usize;
    if buf.len() <= len { return None }
    let ret = std::str::from_utf8(&buf[1..=len]);
    ret.ok().map(|ret| (ret.to_owned(), len + 1))
  }
}

#[cfg(test)]
mod tests {
    // importing names from outer scope
    use super::*;

    // |_ x / y _|
    fn ceil_div(x : usize, y : usize) -> usize {
      (x + y - 1) / y
    }

    #[test]
    fn test_u8_deserialise () {
        let buf: Vec<u8> = vec![1, 2];
        assert_eq!(Some((1, 1)), u8::deserialise(&buf));
    }

    #[test]
    fn test_u8_serialise_inv () {
        let byte = 1u8;
        let ser = u8::serialise(byte);
        assert_eq!(Some(vec![byte]),ser);
        assert_eq!(Some((byte, 1)), u8::deserialise(&ser.unwrap()));
    }

    #[test]
    fn test_u8_deserialise_inv () {
        let byte = 1u8;
        let byte_sing = vec![byte];
        let bind = &[byte_sing.clone()].concat();
        let deser : Option <(u8, usize)> = u8::deserialise(bind);
        assert_eq!(Some((byte, 1)),deser);
        assert_eq!(Some(byte_sing), u8::serialise(byte));
    }

    #[test]
    fn test_u16_serialise_inv () {
        let byte = 255u8;
        let ser = u8::serialise(byte);
        assert_eq!(Some(vec![byte]),ser);
        assert_eq!(Some((byte, 1)), u8::deserialise(&ser.unwrap()));
    }

    #[test]
    fn test_u16_deserialise_inv () {
        let byte = 1u8;
        let byteu16 = byte as u16;
        let byte_sing = vec![0, byte];
        let append = vec![2u8,3,4];
        let bind = &[byte_sing.clone(),append.clone()].concat();
        let deser : Option <(u16, usize)> = u16::deserialise(bind);
        assert_eq!(Some((byteu16, 2)), deser);
        assert_eq!(Some(byte_sing), u16::serialise(byteu16));
    }

    #[test]
    fn test_u16_deserialise_fail () {
        let buf: Vec<u8> = vec![1];
        assert_eq!(None, u16::deserialise(&buf));
        let buf: Vec<u8> = vec![];
        assert_eq!(None, u16::deserialise(&buf));
    }

    #[test]
    fn test_u32_deserialise_fail () {
        let buf: Vec<u8> = vec![1,2,3];
        assert_eq!(None, u32::deserialise(&buf));
        let buf: Vec<u8> = vec![];
        assert_eq!(None, u32::deserialise(&buf));
    }

    #[test]
    fn test_u64_deserialise_zero () {
        let buf: Vec<u8> = vec![0,0,0,0,0,0,0,0,];
        assert_eq!(Some (buf), 0u64.serialise());
    }

    #[test]
    fn test_u64_deserialise_fail () {
        let buf: Vec<u8> = vec![1,2,3,4,5,6,7];
        assert_eq!(None, u64::deserialise(&buf));
        let buf: Vec<u8> = vec![];
        assert_eq!(None, u64::deserialise(&buf));
    }

    #[test]
    fn test_vec_ser() {
      let v: Vec<_> = vec![1u16; 255 * 1 + 45].iter().map(|x| *x as u8).collect();
      let ser = v.serialise();
      assert_eq!(ser, Some([vec![255], vec![1u8; 254], vec![46], vec![1; 46]].concat()));

      let v: Vec<_> = vec![1u16; 255 * 5 + 45].iter().map(|x| *x as u8).collect();
      let ser = v.serialise();
      let ser_eq =
         [vec![255], vec![1u8; 254],
         vec![255], vec![1u8; 254],
         vec![255], vec![1u8; 254],
         vec![255], vec![1u8; 254],
         vec![255], vec![1u8; 254],
         vec![50], vec![1; 50]];
      assert_eq!(ser, Some(ser_eq.concat()));

      let v : Vec<_> = (0u16..(1 * 255 + 45)).map(|x| x as u8).collect();

      let ser = v.serialise();
      let ser_eq =
        [vec![255], (0u8..=253).collect(),
         vec![46, 254, 255], (0u8..=43).collect()].concat();
      assert_eq!(ser, Some(ser_eq));
    }

    #[test]
    fn test_vec_deser() {
      let buf = [vec![255], vec![1u8; 254], vec![46], vec![1; 46]].concat();
      let deser : Option <(Vec<u8>, usize)> = Vec::<u8>::deserialise(&buf);
      let res = vec![1u8; 255 * 1 + 45];
      assert_eq!(deser, Some((res,buf.len())));

      let buf =
        [vec![255], (0u8..=253).collect(),
          vec![255, 254, 255], (0u8..=251).collect(),
          vec![255, 252, 253, 254, 255], (0u8..=249).collect(),
          vec![46, 250, 251, 252, 253, 254, 255], (0u8..=39).collect()].concat();
      let deser : Option <(Vec<u8>, usize)> = Vec::<u8>::deserialise(&buf);
      let deser_eq : Vec<_> = (0u16..=(3 * 256 + 39)).map(|x| x as u8).collect();
      let deser_eq_len = deser_eq.len();
      let additional_symbols = ceil_div(deser_eq_len, 255);
      assert_eq!(deser.as_ref().unwrap().1, deser_eq_len + additional_symbols);
      assert_eq!(deser.as_ref().unwrap().0, deser_eq);

    }

    #[test]
    fn test_pair_serialise_inv () {
        let pair = (255u8,1u8);
        let ser = pair.serialise();
        assert_eq!(Some(vec![pair.0,pair.1]),ser);
        assert_eq!(Some(((pair.0, pair.1), 2)), <(u8,u8)>::deserialise(&ser.unwrap()));
    }

    #[test]
    fn test_string_serialise_inv () {
        let string : String = "abc".to_owned();
        let ser = string.clone().serialise();
        assert_eq!(Some(vec![3,97,98,99]),ser);
        assert_eq!(Some((string, 4)), <String>::deserialise(&ser.unwrap()));
    }

} // mod test

