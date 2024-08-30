#!/usr/bin/env bash

# https://frejaeid.com/rest-api/Freja%20eID%20Relying%20Party%20Developers'%20Documentation.html
# https://frejaeid.com/rest-api/Signature%20Service.html

source functions.sh
CERT="freja-signing.pub"
CERT="DiZbzBfysUm6-IwI-GtienEsbjc.pub"
CERT="2LQIrINOzwWAVDhoYybqUcXXmVs.pub"

# Using JWS Compact Serialization - a compact, URL-safe serialization
# Compact = All header fields are protected
# BASE64URL(UTF8(JWS Protected Header)) || '.' ||
# BASE64URL(JWS Payload) || '.' ||
# BASE64URL(JWS Signature)

FILE="sign_getOneSignResultRequest.json"
test -r "$FILE" || exit

# jq . "$FILE"
details="$(jq --raw-output '.details' $FILE )"

# FILE="aman_vote_050224.json"
# FILE="arve_vote_050224.json"
# FILE="$VCSDIR/ffi/test/new_signed_vote.json"
# details="$(jq --raw-output '.signature' $FILE )"

# JWS Protected Header
# {
#    "x5t":"SHA-1 digest of the signing certificate",
#    "alg":"algorithm used to secure the JWS"
# }
# x5t: mandatory, Base64URL encoding of the certificate's SHA-1 digest.
# alg: mandatory, the value shall be RS256 which corresponds to 'RSA PKCS#1 signature with SHA-256'.

jws_p_header_enc="$(echo -en "$details" | cut -f1 -d. )"
jws_p_header="$(echo -en "$jws_p_header_enc" | base64url_decode | jq .)"
echo "$jws_p_header"
CERTNAME="$(echo -en "$jws_p_header" | jq .x5t --raw-output )"
ls -1 "$CERTNAME.pub"

echo "SHA-1 digest of used certificate:"
echo "$jws_p_header"| jq --raw-output '.x5t' | base64url_decode | xxd -C -l 120 -plain | sed 's/../&:/g; s/:$//' | tr 'a-z' 'A-Z'
echo "Openssl certificate:"
openssl x509 -in "$CERTNAME.pub" -noout -sha1 -fingerprint | cut -f2 -d=
echo

# JWS Payload
# timestamp: Long, mandatory. Describes the time when the confirmation by the end user was validated on Freja eID server side. Expressed in milliseconds, since January 1, 1970, 00:00 UTC.
# signatureData: {
#   userSignature: JWS User Signature
#      sign_user_content . sign_user_signature
#   certificateStatus: OCSP state of end-user certificate
#      sign_user_ocsp
# }

jws_payload="$(echo -en "$details" | cut -f2 -d. | base64url_decode )"
echo "payload:"
echo -en "$jws_payload" | jq .

# tr-filtering because jq adds a trailing \n to $details
echo -en "$details" | cut -f1-2 -d. | tr -dc '[:alnum:].' > "$FILE.vote"
echo -en "$details" | cut -f3 -d. | base64url_decode > "$FILE.sign"

openssl dgst -sha256 -verify "$CERTNAME.pub" -signature "$FILE.sign" "$FILE.vote"


echo "user content"

user_email="$(echo -en "$jws_payload" | jq -r '.userInfo')"

user_details="$(echo -en "$jws_payload" | jq --raw-output '.signatureData.userSignature')"
user_header="$(echo -en "$user_details" | cut -f1 -d.)"
user_header_protected="$(echo -en "$user_header" | base64url_decode | jq '{ alg }' | tr -dc '[:alnum:]":{[]}' | base64url_encode )"
user_payload="$(echo -en "$user_details" | cut -f2 -d.)"
echo -en "$user_details" | cut -f1-2 -d. | tr -dc '[:alnum:].' > sign_user_content
echo -en "$user_details" | cut -f3 -d. | base64url_decode > sign_user_signature

echo "text signed by user"
echo -en "$user_payload" | base64url_decode | jq -r '.text' | base64url_decode
echo "data signed by user"
echo -en "$user_payload" | base64url_decode | jq -r '.binaryData' | base64url_decode

