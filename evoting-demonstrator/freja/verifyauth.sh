#!/usr/bin/env bash

source functions.sh

CERT="freja-signing.pub"

# Using JWS Compact Serialization - a compact, URL-safe serialization
# Compact = All header fields are protected
# BASE64URL(UTF8(JWS Protected Header)) || '.' ||
# BASE64URL(JWS Payload) || '.' ||
# BASE64URL(JWS Signature)

FILE="auth_getOneResult.json"
test -r "$FILE" || exit

details="$(jq --raw-output '.details' $FILE)"

# example: details="eyJ4NXQiOiIyTFFJcklOT3p3V0FWRGhvWXlicVVjWFhtVnMiLCJhbGciOiJSUzI1NiJ9.eyJzdGF0dXMiOiJBUFBST1ZFRCIsInVzZXJJbmZvVHlwZSI6IklORkVSUkVEIiwidXNlckluZm8iOiJOL0EiLCJ0aW1lc3RhbXAiOjE2NTg5OTI1ODIwMTcsIm1pblJlZ2lzdHJhdGlvbkxldmVsIjoiQkFTSUMiLCJyZXF1ZXN0ZWRBdHRyaWJ1dGVzIjp7ImVtYWlsQWRkcmVzcyI6ImFydmVnQGt0aC5zZSJ9LCJhdXRoUmVmIjoidkpoRFc4enA3MlhyNG5xeXViZF9zd0x5Y21wMzg1YUdlVVBmMmtCd18yMzRydzBSTWxqNmNsQlNGVi04akJWZyJ9.K5nlad2ta5yv_Bzev4y0c8MY1L8YHNioQXI9ACAFn_gtJZhGTIOpExFTXBa4yanGlIEZAAZ13XABg_erNYlehMW0l7nEh2fxDje8zorbxWh3Mh1NgGpslNTbqkfx0UTlh7LL6tfSAgVVpQy4lnlEnFYnHl50o_kTrrKtSCNTAqzELy0fVqgeYbRiKUSHPBO0-WYC7IdcelpjYtv_3I_Y_79YkkG9eD0xkN4JwKkuBItlmJOLPG3ojS2dOnG5XCtRQe1qPkdgj5xqJwGaCYyvOlQdzcQtFjcr3eHZl5u2Pipz_ePkR4yQB6L2rPsCrAn5Di7hm4maIJYHN4eS4CBgaQ"

# JWS Protected Header
# {
#    "x5t":"SHA-1 digest of the signing certificate",
#    "alg":"algorithm used to secure the JWS"
# }
# x5t: mandatory, Base64URL encoding of the certificate's SHA-1 digest.
# alg: mandatory, the value shall be RS256 which corresponds to 'RSA PKCS#1 signature with SHA-256'.
protected_header_enc="$(echo -en "$details" | cut -f1 -d. )"
protected_header="$(echo -ne "$protected_header_enc" | base64url_decode | jq .)"
echo "$protected_header"

echo "algorithm: $(echo $protected_header | jq --raw-output '.alg')"

echo "SHA-1 digest of used signature certificate:"
echo $protected_header | jq --raw-output '.x5t' | base64url_decode | xxd -C -l 120 -plain | sed 's/../&:/g; s/:$//' | tr 'a-z' 'A-Z'
echo "SHA-1 digest of openssl certificate:"
openssl x509 -in "$CERT" -noout -sha1 -fingerprint | cut -f2 -d=
echo

payload_enc="$(echo -en "$details" | cut -f2 -d. )"
payload="$(echo -ne "$payload_enc" | base64url_decode | jq .)"
echo "payload:"
echo "$payload"

echo -en "$protected_header_enc.$payload_enc" > auth_content
echo -en "$details" | cut -f3 -d. | base64url_decode > auth_sign

openssl dgst -sha256 -verify "$CERT" -signature auth_sign auth_content

