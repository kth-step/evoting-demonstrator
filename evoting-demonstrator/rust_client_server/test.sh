#!/usr/bin/env dash
# application/x-www-form-urlen‐coded
# vote=$(cat vote.json | python -c "import urllib.parse, sys; print (urllib.parse.quote(  sys.argv[1] if len(sys.argv) > 1 else sys.stdin.read()[0:-1]));")
curl "127.0.0.1:7878" --data-urlencode "ballot@vote.json"


