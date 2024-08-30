#!/usr/bin/env bash

python clientctl.py --socket /tmp/primary.sock put "a" "a"
python clientctl.py --socket /tmp/primary.sock put "a" "b"
python clientctl.py --socket /tmp/primary.sock put "b" "b"
python clientctl.py --socket /tmp/primary.sock put "c" "c"
python clientctl.py --socket /tmp/primary.sock get "a"
python clientctl.py --socket /tmp/primary.sock read

