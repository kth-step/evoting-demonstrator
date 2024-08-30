
TESTNAME="$(basename "$1" ".sh")"
TEST="$1"

if test ! -r "$TEST"; then
  echo "test not found: '$TEST'"
  echo "usage $0 <test file>"
  exit
fi


if test ! -r "$UNVERIF"; then
  echo "environment variable required: '\$UNVERIF'"
  exit
fi

id="$(date "+%Y%m%d-%H%M%S")_${TESTNAME}"
LOGDIR="$VCSDIR/tests/logs"

make -C "$UNVERIF" run_mixnet    &> "$LOGDIR/${id}_mixnet.log" &
PID_MIXNET="${!}"

make -C "$UNVERIF" run_webserver &> "$LOGDIR/${id}_webserver.log" &
PID_VCS="${!}"

make -C "$UNVERIF" run_auth &> "$LOGDIR/${id}_auth.log" &
PID_AUTH="${!}"

sleep 4

# principal test
/usr/bin/time --output="$LOGDIR/${id}_timing.log" sh "$TEST"

echo
for x in $PID_VCS $PID_MIXNET $PID_AUTH \
  $(ps auxwf | grep 'gunicorn' | grep -v grep | awk '{print $2}'); do
  /usr/bin/kill --verbose --timeout 1000 TERM --timeout 1000 KILL --signal QUIT "$x"
done
echo "waiting for processes to finish"
wait

