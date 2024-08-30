
# Description

The scripts contained in this folder enable authentication and signing with
Freja eID. They require [`jq`](https://stedolan.github.io/jq/) for parsing
JSON, [`curl`](https://curl.se/) for networking and having the secrets in
place.

Files:
```
authentication.sh - Authentication workflow
signing.sh        - Signing workflow
freja-signing.pub - freja public signing key
verifyauth.sh     - verify an authentication
verifysign.sh     - verify a signature
functions.sh      - common functions
```

Secrets not in the repository:
```
kth.pfx - Binary compiled SSL/TLS certificate (containing crt and key)
kth.crt - Certificate
kth_derivedkey.enc  - encrypted private key
kth_derivedkey.pass - passphrase for the above
kth_derivedkey.key  - (decrypted) private rsa key
```

# Obtaining the certificate

```bash
SERVER="https://services.test.frejaeid.com"
openssl s_client -showcerts -servername "$SERVER" -connect "$SERVER:443" > "$CACERT"
```

# Split pfx into key and crt

```bash
# extract certificate from pfx
openssl pkcs12 -in kth.pfx -clcerts -nokeys -out kth.crt
```

```bash
# extract a new private *.key from *.pfx
openssl pkcs12 -in kth.pfx -nocerts -out kth_derivedkey.enc
# extract *.key from encrypted *.enc
openssl rsa -aes256 -in kth_derivedkey.enc -out kth_derivedkey.key
# extract public key from encrypted
openssl rsa -aes256 -in kth_derivedkey.enc -pubout -out kth_derivedkey.pub
# decrypt key without password
openssl rsa -in kth_derivedkey.enc -out kth_derivedplain.key
```



## Testing
```bash
openssl s_client -pass "file:kth_derivedkey.pass" -verify_return_error -CAfile cacert.pem -cert kth.crt -key kth_derivedkey.key -connect services.test.frejaeid.com:443
curl --cacert cacert.pem --cert kth.crt --key kth_derivedkey.key --pass "..." https://services.test.frejaeid.com
```


## Signing

For signing there are [different certificates](https://frejaeid.com/rest-api/Freja%20eID%20Relying%20Party%20Developers'%20Documentation.html), depending on the time range.
The received data is encoded using JWS Compact Serialization - a compact, URL-safe serialization:
```
BASE64URL(UTF8(JWS Protected Header)) || '.' ||
BASE64URL(JWS Payload) || '.' ||
BASE64URL(JWS Signature)
```

To verify that the payload matches its signature use

```bash
# show details about this certificate
openssl x509 -in freja-signing.cert -noout -text
#  extract public key from certificate
openssl x509 -in freja-signing.cert -pubkey -noout freja-signing.pub
# verify payload `jws_payload.txt` with `jws_signature.sig`
openssl dgst -sha256 -verify freja-signing.pub -signature jws_signature.sig jws_payload.txt
```

