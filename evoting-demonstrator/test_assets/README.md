
# Fabricate `*.pub` from `*.pem`

```sh
openssl x509 -inform pem -in DiZbzBfysUm6-IwI-GtienEsbjc.pem -pubkey -out DiZbzBfysUm6-IwI-GtienEsbjc.pub
openssl x509 -in DiZbzBfysUm6-IwI-GtienEsbjc.pub -out DiZbzBfysUm6-IwI-GtienEsbjc.der -outform DER 
openssl x509 -inform pem -in 2LQIrINOzwWAVDhoYybqUcXXmVs.pem -pubkey -out 2LQIrINOzwWAVDhoYybqUcXXmVs.pub
openssl x509 -in 2LQIrINOzwWAVDhoYybqUcXXmVs.pub -out 2LQIrINOzwWAVDhoYybqUcXXmVs.der -outform DER 
```

# Fabrication of `signed_vote.json` (old format)

The signed vote is currently obtained from `enc_vote.plain` as follows:

```bash
xxd -r -p enc_vote.plain > enc_vote
# compare
vimdiff <(fold -w 60 enc_vote.plain) <(xxd -p enc_vote)
# hash supposed to have been signed jws.json
sha256sum enc_vote
# payload
cat <<EOF > signed_vote.json
{"vote": "$(basenc --wrap=0 --base64url enc_vote | tr -d '=')",
"signature": "$(jq --raw-output .details jws.json)"}
EOF
```

# JSON vote parameter extraction and signature verification

```bash
#hash contained in
#.details | snd | .signatureData.userSignature | snd | base64url_decode | .text

VCSDIR="$(pwd)/.."
FILE="$VCSDIR/test_assets/new_signed_vote.json"
FILE="$VCSDIR/test_assets/aman_vote_240205.json"
FILE="$VCSDIR/test_assets/arve_vote_240205.json"
FILE="$VCSDIR/test_assets/arve_vote_240201.json"

echo "$FILE"

json.cake -k '["signature"]' "$FILE" \
| cut -d. -f2 | tr -dc '[:alnum:].\-+' | base64.cake -d -u \
| json.cake -k '["signatureData","userSignature"]' | cut -d. -f2 | tr -dc '[:alnum:].\-+' | base64.cake -d -u \
> "$FILE.hash"
cat "$FILE.hash"

# Certificate name in x5t

CERTNAME="$(json.cake -k '["signature"]' "$FILE" \
| cut -d. -f1 | tr -dc '[:alnum:].' | base64.cake -d -u \
| json.cake -k '["x5t"]' | tr -d '"')"
ls -1 "$CERTNAME.pub"

# re-extract the binary vote (old format: base64 encoded binary data)

json.cake -k '["vote"]' "$FILE" \
| tr -dc '[:alnum:].+/' \
| base64.cake -d > "$FILE.enc_vote"
cat "$FILE.enc_vote"
sha256sum "$FILE.enc_vote"

# re-extract the binary vote (new format: hexstring)

json.cake -k '["vote"]' "$FILE" \
| tr -dc '[:alnum:].+/' \
| xxd -r -p > "$FILE.enc_vote"
cat "$FILE.enc_vote"
sha256sum "$FILE.enc_vote"

# reextract signed payload

json.cake -k '["signature"]' "$FILE" \
| cut -f1-2 -d. | tr -dc '[:alnum:].\-+_' \
> "$FILE.payload"
sha256sum "$FILE.payload"
wc -c "$FILE.payload"

# re-extract signature

json.cake -k '["signature"]' "$FILE" \
| cut -f3 -d. | tr -dc '[:alnum:].\-+_' \
| base64.cake -d -u > "$FILE.sign"
wc -c "$FILE.sign"

# verification

ls -1 "$CERTNAME.pub"
openssl dgst -sha256 -verify "$CERTNAME.pub" -signature "$FILE.sign" "$FILE.payload"

# extract user signature

json.cake -k '["signature"]' "$FILE" \
| cut -d. -f2 | tr -dc '[:alnum:].\-+' \
| base64.cake -d -u \
| json.cake -k '["signatureData","userSignature"]' \
| tr -dc '[:alnum:].\-+' \
> "$FILE.user_sign"


# Transform from new to old vote format


cat <<EOF > "$FILE.oldformat"
{"vote": "$(json.cake -k '["vote"]' "$FILE" | tr -dc '[:alnum:]' | xxd -r -p | base64.cake | tr -d '=')",
"signature": $(json.cake -k '["signature"]' "$FILE")}
EOF
wc "$FILE.oldformat"

# Craft a wrong JWS

cat <<EOF > "$FILE.wrongjws"
{"vote": "$(json.cake -k '["vote"]' "$FILE" | tr -dc '[:alnum:]' | xxd -r -p | base64.cake | tr -d '=')",
"signature": 
"$(json.cake -k '["signature"]' "$FILE" \
| cut -d. -f1 ).$(json.cake -k '["signature"]' "$FILE" \
| cut -d. -f2 | tr -dc '[:alnum:].\-+' \
| base64.cake -d -u \
| jq 'delpaths([["userInfo"]])' \
| base64.cake -u).$(json.cake -k '["signature"]' "$FILE" \
| cut -d. -f3)" }
EOF
wc "$FILE.wrongjws"

```

