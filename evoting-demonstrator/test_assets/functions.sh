
# add padding to signature
function padding() {
  content="$(if [ "$#" -gt 0 ]; then echo -en "$1"; else cat -; fi)"
  len="$(( "$(echo -en "$content" | wc -c)" % 4 ))"
  pad=""
  if [[ ! "$len" -eq 0 ]]; then
    pad="$(printf -- '=%.0s' $(seq 3 -1 "$len"))"
  fi
  echo "$content$pad"
}

# decode and add padding
function base64_decode (){
  { if [ "$#" -gt 0 ]; then echo -en "$1"; else cat -; fi ; } \
    | padding \
    | basenc -i -d --base64 --wrap=0
}

# decode and add padding
function base64url_decode (){
  { if [ "$#" -gt 0 ]; then echo -en "$1"; else cat -; fi ; } \
    | padding \
    | basenc -i -d --base64url --wrap=0
}

# encode with padding
function base64url_encode_pad (){
  { if [ "$#" -gt 0 ]; then echo -en "$1"; else cat -; fi ; } \
    | basenc -i --base64url --wrap=0
}

# encode without padding
function base64url_encode (){
  { if [ "$#" -gt 0 ]; then echo -en "$1"; else cat -; fi ; } \
    | base64url_encode_pad | sed -E 's/=+$//'
}

