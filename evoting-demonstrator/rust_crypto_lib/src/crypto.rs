use hacspec_lib::*;
use hacspec_rsa_pkcs1::*;

// source of to_hex (no licence)
// https://gist.github.com/Salpadding/c4c29872e74a1d4aff20ce2e8df2b803
static CHARS: [char; 16] = ['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f',];

pub fn to_hex(data: &[u8]) -> String {
    let mut s = String::with_capacity(data.len() * 2);
    for i in data {
        s.push(CHARS[((i >> 4) & 0x0f) as usize]);
        s.push(CHARS[(i & 0x0f) as usize]);
    }
    s
}

pub fn sha256(bytes: &[u8]) -> [u8; 32] {
    let bytes= Seq::<U8>::from_public_slice(bytes);
    let digest = hacspec_sha256::sha256(&bytes);
    digest.to_public_array()
}

// the public key for freja
fn freja_pub_key() -> (RSAInt, RSAInt) {
/*
    export FILE="$VCSDIR/test_assets/2LQIrINOzwWAVDhoYybqUcXXmVs.pub"
    export FILE="$VCSDIR/test_assets/DiZbzBfysUm6-IwI-GtienEsbjc.pub"
    sed -n '/BEGIN PUBLIC KEY/,/END PUBLIC KEY/p'  "$FILE" > rsakey
    grep -v PUBLIC rsakey | tr -dc '[[:print:]]' | base64 -d | xxd -plain
    # parse public key to extract n and d
    openssl asn1parse -in rsakey -inform PEM
    # https://datatracker.ietf.org/doc/html/rfc2313#section-7.1
    19:d=1  hl=4 l= 271 prim: BIT STRING
    openssl asn1parse -strparse 19 -in rsakey -inform PEM
    4: d=1 hl=4 l=257 prim:  INTEGER ... (modulus)
    prim: INTEGER : 01 00 01 == 2^16 + 1
*/

    // 2LQIrINOzwWAVDhoYybqUcXXmVs From 2020-05-13
    // https://www.frejaeid.com/tc/jwscerts/2LQIrINOzwWAVDhoYybqUcXXmVs.pem
    let n2020 = "80C20DB3CED38A8B833D24A6A67D39919BFD4CDF17768A5C1E7125A7A12524BA50877A181882F807BD68220177AFCCD15AAF2442826560CBA09A1B25774AF412C5096ECADC8C1279089D5661983556EF05A582CAA1A15123FAB14FAC4232F776DFC43DF52765E86E8EF6C410A05AB5D0469805AF7BD139779C3CE2410E9B6D2364668398219A22731E3ED5716CAC68ABBBCA3C408C9CDE0D1E4A0ADDDDEB1B524BA4D1E1FAE5279A68E0ABB1A08EA4952A133883F9E97847A778D1D4F3FEEC5698DA46285E019AC3567908BD6F880362E16A35886CEDB9DA86F90AE8BBED0D3855EFDDFDE69C7FA14CF90440DD5708F13C9CE0680B941C4FBA03574C6A9923B1";

    // DiZbzBfysUm6-IwI-GtienEsbjc From 2023-02-23
    // https://www.frejaeid.com/tc/jwscerts/DiZbzBfysUm6-IwI-GtienEsbjc.pem
    let n2023 = "E232D8615A4653F4EBF27BCAB32692FF8C740E0E455452F413BEB13BBA11BCACB29FC9AD76E57CC8A9F08096D6B3A5F1D2F1EE28D5C7C44FD3C9D5882C32570452CCCCA60BC36C17819B6F0B8A91549359E35D3B46577F7E950F3C28BA531CA8513D1C4476646970CB97D6D1C3D776B73748F085C016AC5B992EC8A178FD62EF134A75AD91A27B6C837A6B14FB73638B16F643B55107CE79C6B2FCCA88A466ECB87EE441B203AD8D7C6754CD5FC61173913E2BAF60653065FA92E38E9672E3D3F4D87AE2280DDAF2EA54D10292AA2A3C5F5A649650695E222389BF87C68CDEEB1AA71DF8B78875E274D8EDC6C6A6F1BFA0C3069F2A948215F97FAECC13A4F351";

    let e = "010001";
    let n = RSAInt::from_hex(n2023);
    let e = RSAInt::from_hex(e);
    (n, e)
}

/// generates the constant padding prefix for a SHA256 hash (512 bit - 256/16)
fn emsa_pkcs1_v1_5_sha256() -> String {
    // 9.2.  EMSA-PKCS1-v1_5
    // https://datatracker.ietf.org/doc/html/rfc8017#section-9.2
    // 0x00 || 0x01 || PS || 0x00
    // PS is 404 * 16 bit long
    // 38 * 16 bit of SHA256 digestAlgorithm AlgorithmIdentifier
    // hash length 64 letters * 16 (hex) = 256
    let h_len = 64;
    // ASN.1 value of type DigestInfo sha256
    let sha256_digestinfo_enc = "3031300d060960864801650304020105000420";
    let ps_len = 512 - 6 - h_len - sha256_digestinfo_enc.len();
    let prefix = "0001".to_string() + &"f".repeat(ps_len) + "00";
    prefix + sha256_digestinfo_enc
}

pub fn verify_rs256(
    signature      : &[u8],
    content        : &[u8],
) -> bool {

    let content_seq = Seq::from_vec(content.iter().map(|x| U8::classify(*x)).collect());
    let content_hash = hacspec_sha256::sha256(&content_seq).to_hex();
    let signature_seq = Seq::<u8>::from_native_slice(&signature);
    let s: RSAInt = RSAInt::from_public_byte_seq_be(signature_seq);
    let rsaint = rsavp1(freja_pub_key(), s).unwrap();
    let hashseq = rsaint.to_byte_seq_be();
    let hashseq_str = ByteSeq::to_hex(&hashseq);
    let prefix = emsa_pkcs1_v1_5_sha256();
    let hash_enc = prefix + &content_hash;
    hashseq_str == hash_enc

    /*
    // for debugging
      let len : u32 = 2048u32 / 8u32;
      let (pre,hash) = &hashseq_str.split_at(hashseq_str.len() - 64);
      let (hd,digestinfo) = &pre.split_at(pre.len() - sha256_digestinfo_enc.len());

      println!("decrypted hex {}", hashseq_str);
      println!("signed hash {}", hash);

      println!("hash eq {}", hash == &content_hash);
      println!("digest info eq {}", digestinfo == &sha256_digestinfo_enc);
      println!("prefix eq {}", hd == &prefix);
    */
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn crypto_verify_rs256_test() {
        let path = "../test_assets/";

        let content = fs::read(path.to_string()  + "arve_vote_240205.json.payload").expect("Could not read payload file");
        let signature = fs::read(path.to_string() + "arve_vote_240205.json.sign").expect("Could not read signature file");

        println!("signature len {}, content len {}", signature.len(), content.len());
        assert!(verify_rs256(&signature,&content,));
    }

    #[test]
    fn test_to_hex () {
        let bytes: [u8;32] = [39,170,186,193,213,72,158,207,214,173,182,86,0,250,137,188,119,237,104,208,12,250,54,89,57,154,218,169,128,174,191,64];

        assert_eq!(to_hex(&bytes), "27aabac1d5489ecfd6adb65600fa89bc77ed68d00cfa3659399adaa980aebf40")
    }
}

