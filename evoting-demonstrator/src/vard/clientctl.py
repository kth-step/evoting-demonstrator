import argparse
import os
import sys
import pathlib

import client

# example call:
# python clientctl.py --socket /tmp/primary.sock put "a" "a"
# python clientctl.py --socket /tmp/primary.sock get "a"
# python clientctl.py --socket /tmp/primary.sock read

def create_client(args):
    return client.Client(args.socket)

def read(args):
    client = create_client(args)
    client.read()
    data = client.recv_all()
    init_data = data[0:min(len(data),30)]
    print(f"received data head: {init_data} len: {len(data)}")
    client.disconnect()

def get(args):
    client = create_client(args)
    client.get(args.key)
    data = client.recv_all()
    init_data = data[0:min(len(data),30)]
    print(f"received data head: {init_data} len: {len(data)}")
    client.disconnect()

def put(args):
    client = create_client(args)
    client.put(args.key, args.value)
    data = client.recv_all()
    init_data = data[0:min(len(data),30)]
    print(f"received data head: {init_data} len: {len(data)}")
    client.disconnect()

def main():
    parser = argparse.ArgumentParser()

    parser.add_argument('--socket', type=pathlib.Path,
                        help='path to unix domain socket')

    # subcommands
    subparsers = parser.add_subparsers(dest='cmd', help='commands')

    subparsers.add_parser('read', help='Issue read')

    get_parser = subparsers.add_parser('get', help='Issue GET request')
    get_parser.add_argument('key', action='store', help='Key to GET')

    put_parser = subparsers.add_parser('put', help='Issue PUT request')
    put_parser.add_argument('key', action='store', help='Key to PUT')
    put_parser.add_argument('value', action='store', help='Value to PUT')

    args = parser.parse_args()
    globals()[args.cmd](args)

if __name__ == '__main__':
    main()

