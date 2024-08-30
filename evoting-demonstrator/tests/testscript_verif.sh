
TESTNAME="$(basename "$1" ".sh")"
TEST="$1"

if test ! -r "$TEST"; then
  echo "test not found: '$TEST'"
  echo "usage $0 <test file>"
  exit
fi

id="$(date "+%Y%m%d-%H%M%S")_${TESTNAME}"
LOGDIR="$VCSDIR/tests/logs"

make -C "$VCSDIR/emulation" emulation
make -C "$VCSDIR/emulation" run_vcs    &> "$LOGDIR/${id}_vcs.log" &
PID_VCS="${!}"
sleep 4
make -C "$VCSDIR/emulation" run_client &> "$LOGDIR/${id}_client.log" &
PID_CLIENT="${!}"
sleep 4
make -C "$VCSDIR/emulation" run_admin  &> "$LOGDIR/${id}_admin.log" &
PID_ADMIN="${!}"
#pushd "$VCSDIR/rust_client_server"
#SERVER_ADDRESS="127.0.0.1:7878" cargo run &> "$LOGDIR/${id}_client_srv.log" &
#PID_CLIENT_SRV="${!}"
#popd

# principal test
/usr/bin/time --output="$LOGDIR/${id}_timing.log" sh "$TEST"

echo
for x in $PID_VCS $PID_CLIENT $PID_ADMIN $PID_CLIENT_SRV \
  $(ps auxwf | grep 'emulation ' | grep -v grep | awk '{print $2}'); do
  /usr/bin/kill --verbose --timeout 1000 TERM --timeout 1000 KILL --signal QUIT "$x"
done
echo "waiting for processes to finish"
wait

