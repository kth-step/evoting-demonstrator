#!/usr/bin/env bash

# https://frejaeid.com/rest-api/Authentication%20Service.html

SERVER="https://services.test.frejaeid.com"

CACERT="cacert.pem"
test -r "$CACERT" || { echo "No root certificate $CACERT found" ; exit ; }
CERT="kth.crt"
test -r "$CERT" || { echo "No certificate $CERT found" ; exit ; }
KEY="kth_derivedkey.key"
test -r "$KEY" || { echo "No key $KEY found" ; exit ; }
PASS="kth_derivedkey.pass"
test -r "$PASS" || { echo "No passphrase $PASS found" ; exit ; }

pass="$(cat kth_derivedkey.pass | tr -dc '[:print:]')"
CURL="curl --cacert $CACERT --cert $CERT --key $KEY --pass $pass"

# https://gist.github.com/cdown/1163649
url_encode() {
  old_lc_collate=$LC_COLLATE
  LC_COLLATE=C
  local length="${#1}"
  for (( i = 0; i < length; i++ )); do
    local c="${1:$i:1}"
    case $c in
      [a-zA-Z0-9.~_-]) printf '%s' "$c" ;;
      *) printf '%%%02X' "'$c" ;;
    esac
  done
  LC_COLLATE=$old_lc_collate
}
url_decode() {
  local url_encoded="${1//+/ }"
  printf '%b' "${url_encoded//%/\\x}"
}

# initAuthRequest
# alternative DATA for any user to login
read -r -d '' DATA <<EOF
{
  "userInfoType":"INFERRED",
  "userInfo":"N/A",
  "attributesToReturn": [
    {"attribute":"EMAIL_ADDRESS"}
  ]
}
EOF
# alternative DATA for specific user
read -r -d '' DATA <<EOF
{
  "userInfoType":"EMAIL",
  "userInfo":"arveg@kth.se",
  "attributesToReturn": [],
  "minRegistrationLevel": "BASIC"
}
EOF
DATA_enc="$(echo -ne "${DATA}" | base64)"

$CURL \
  -X POST \
  --data "initAuthRequest=${DATA_enc}" \
  --output "auth_initAuthRequest.json" \
  "$SERVER/authentication/1.0/initAuthentication"

FILE="auth_initAuthRequest.json"
if test -r "$FILE"; then
  authref="$(jq --raw-output '.authRef' $FILE)"
  url_string="frejaeid://bindUserToTransaction?transactionReference=${authref}"
  if { command -v qrencode && command -v xdg-open ; } 2>/dev/null 1>&2 ; then
    # generate qr code to scan
    qrencode "$url_string" -o "authRef.png" --type=PNG && \
      xdg-open "authRef.png" & disown
  else
    # let freja generate the qr code
    echo "Scan the QR code at:"
    echo "https://resources.test.frejaeid.com/qrcode/generate?qrcodedata=$(url_encode "$url_string")"
  fi
fi

echo "Press any key to continue. Ctrl-c aborts."
while : ; do
  read -n 1
  if [ $? = 0 ] ; then
    break ;
  fi
done

# getOneAuthResultRequest
$CURL \
  -X POST \
  --data "getOneAuthResultRequest=$(base64 "auth_initAuthRequest.json")" \
  --output "auth_getOneResult.json" \
  "$SERVER/authentication/1.0/getOneResult"

jq . "auth_getOneResult.json" | less


# getAuthResultsRequest
read -r -d '' DATA <<EOF
{
   "includePrevious":"ALL"
}
EOF
DATA_enc="$(echo -ne "${DATA}" | base64)"

$CURL \
  -X POST \
  --data "getAuthResultsRequest=${DATA_enc}" \
  --output "auth_getResults.json" \
  "$SERVER/authentication/1.0/getResults"

jq . "auth_getResults.json" | less

