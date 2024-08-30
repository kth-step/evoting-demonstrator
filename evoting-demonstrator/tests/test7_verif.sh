cd "$VCSDIR/rust_app_lib" && cargo run --bin=input_admin_start
curl "127.0.0.1:7878" --data-urlencode "ballot@$VCSDIR/test_assets/aman_vote_240205.json"
curl "127.0.0.1:7878" --data-urlencode "ballot@$VCSDIR/test_assets/arve_vote_240205.json"
