pub mod cli;
pub mod deserialise;
pub mod select;

// write a number to a vector at offset, offset+1
pub fn int_to_byte2_offset(num: i16, buf: &mut [u8], offset: usize) {
  assert!(offset + 1 < buf.len());
  let bytes = num.to_be_bytes();
  buf[offset] = bytes[0];
  buf[offset + 1] = bytes[1];
}

// read a number from a vector at offset, offset+1
pub fn byte2_to_int_offset(buf: &[u8], offset: usize) -> i16 {
  assert!(offset + 1 < buf.len());
  let bytes = [buf[offset], buf[offset + 1]];
  i16::from_be_bytes(bytes)
}
