#!/usr/bin/env bash

# https://frejaeid.com/rest-api/Signature%20Service.html
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

hash="$( cat /dev/urandom| head -1 | sha1sum | cut -f1 -d' ' )"
formattedhash="$(echo -n "$hash" | tr -cd '[:alnum:]' | sed 's/..../& /g; s/ $//')"

read -r -d '' textToSign <<EOF
${formattedhash}

Base64 encoded UTF-8 text displayed to the end user, 4096 plain text characters maximum prior to base64
EOF
textToSign_enc="$(echo -ne "${textToSign}" | base64 --wrap=0)"

read -r -d '' binaryToSign <<EOF
Base64 encoded byte array not displayed to the user, 5 MB bytes maximal prior to base64
EOF
binaryToSign_enc="$(echo -ne "${binaryToSign}" | base64 --wrap=0)"

# initSignature
# for milliseconds otherwise use: date +%s%N | cut -b1-13

# "userInfo": "kisama8022@giftcv.com",

read -r -d '' DATA <<EOF
{
  "userInfoType": "EMAIL",
  "userInfo": "arveg@kth.se",
  "minRegistrationLevel": "BASIC",
  "title": "Compare the hash of the encrypted vote and sign it",
  "expiry":"$(date --date="+2 hours" +%s%3N)",
  "pushNotification": {
    "title":"Title to display in push notification to user",
    "text":"Text to display in push notification to user"
  },
  "dataToSignType": "EXTENDED_UTF8_TEXT",
  "dataToSign": {
    "text":"${textToSign_enc}",
    "binaryData":"${binaryToSign_enc}"
  },
  "signatureType": "EXTENDED",
  "attributesToReturn": [
    {"attribute":"EMAIL_ADDRESS"}
  ]
}
EOF

read -r -d '' DATA <<EOF
{
  "userInfoType": "EMAIL",
  "userInfo": "arveg@kth.se",
  "minRegistrationLevel": "BASIC",
  "title": "Compare the hash of the encrypted vote and sign it",
  "expiry":"$(date --date="+2 hours" +%s%3N)",
  "pushNotification": {
    "title":"Title to display in push notification to user",
    "text":"Text to display in push notification to user"
  },
  "dataToSignType": "SIMPLE_UTF8_TEXT",
  "dataToSign": {
    "text":"${textToSign_enc}"
  },
  "signatureType": "SIMPLE",
  "attributesToReturn": [
    {"attribute":"EMAIL_ADDRESS"}
  ]
}
EOF
DATA_enc="$(echo -ne "${DATA}" | base64 --wrap=0)"

$CURL \
  -X POST \
  --data "initSignRequest=${DATA_enc}" \
  --output "sign_initSignRequest.json" \
  "$SERVER/sign/1.0/initSignature"

FILE="sign_initSignRequest.json"
if test -r "$FILE"; then
  signRef="$(jq --raw-output '.signRef' $FILE)"
  echo "signRef: $signRef"
fi

echo "Press any key to fetch signing result. Ctrl-c aborts."
while : ; do
  read -n 1
  if [ $? = 0 ] ; then
    break ;
  fi
  sleep 1
done

# getOneResult
$CURL \
  -X POST \
  --data "getOneSignResultRequest=$(base64 "sign_initSignRequest.json")" \
  --output "sign_getOneSignResultRequest.json" \
  "$SERVER/sign/1.0/getOneResult"

jq . "sign_getOneSignResultRequest.json" | less

# getAuthResultsRequest
read -r -d '' DATA <<EOF
{
   "includePrevious":"ALL"
}
EOF
DATA_enc="$(echo -ne "${DATA}" | base64)"

$CURL \
  -X POST \
  --data "getSignResultsRequest=${DATA_enc}" \
  --output "sign_getSignResultsRequest.json" \
  "$SERVER/sign/1.0/getResults"

jq . "sign_getSignResultsRequest.json" | less

