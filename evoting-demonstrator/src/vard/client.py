import re
from uuid import uuid4
from select import select
# https://docs.python.org/3.10/library/struct.html
from struct import pack, unpack
import socket

class SendError(Exception):
    pass

class ReceiveError(Exception):
    pass

class DeserialiseError(Exception):
    pass

class SerialiseError(Exception):
    pass

class Client(object):

    def __init__(self, sock_file, sock=None):
        self.client_id = uuid4().hex
        self.request_id = 0
        if sock is None:
            self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            self.sock.connect(bytes(sock_file))
        else:
            self.sock = sock
        self.sock.settimeout(1) # second(s)

    def send_client_id(self):
        n = self.sock.send(pack("<H", len(self.client_id)))
        if n < 2:
            raise SendError
        else:
            self.sock.send(self.client_id)

    def recv_all(self):
        data = []
        try:
            while True:
                ret = self.sock.recv(1024)
                if not ret: break
                data.append(ret)
        except TimeoutError:
            pass # ignore
        finally:
            return b''.join(data)

    def disconnect(self):
        self.sock.shutdown(socket.SHUT_RDWR)
        self.sock.close()

    def reconnect(self, sock_file, sock=None):
        self.sock.shutdown(socket.SHUT_WR)
        self.sock.close()
        if sock is None:
            self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            self.sock.connect(bytes(sock_file))
        else:
            self.sock = sock

    def deserialize(self, data):
        if data == '-':
            return None
        return data

    def serialize(self, arg):
        if arg is None:
            return '-'
        return str(arg)

    def serialise_str(self,s):
        return pack('B',len(s)) + s.encode('utf-8')

    def deserialise_str(self,s):
        if len(s) < 1:
            raise DeserialiseError()
        try:
            length = unpack('B',s[0])
            v = (s[0:length]).decode('utf-8')
            return v
        except:
            raise DeserialiseError()

    def serialise_opt(self, opt_str):
        match opt_str:
            case None:
                return b'\x01'
            case s:
                return b'\x00' + self.serialise_str(s)

    def serialise_cmd(self, cmd, arg1=None, arg2=None, arg3=None):
        read_pre = b'\x01'
        match (cmd.upper(),arg1,arg2,arg3):
            case ('PUT',k,v,None):
                return read_pre + b'\x00' + (self.serialise_str(k)) + \
                    (self.serialise_str(v))
            case ('GET',k,None,None):
                return read_pre + b'\x01' + (self.serialise_str(k))
            case ('DEL',k,None,None):
                return read_pre + b'\x02' + (self.serialise_str(k))
            case ('CAS',k,opt,v):
                return read_pre + b'\x03' + (self.serialise_str(k)) + \
                    (self.serialise_opt(opt)) + (self.serialise_str(v))
            case ('CAD',k,v,None):
                return read_pre + b'\x04' + (self.serialise_str(k)) + \
                        (self.serialise_str(v))
            case ('READ', None, None, None):
                return b'\x00'
            case _:
                raise SerialiseError

    def send_command(self, cmd, arg1=None, arg2=None, arg3=None):
        # msg = str(self.request_id) + ' ' + cmd + ' ' + ' '.join()
        # x00 is for 'Request'
        data = self.serialise_cmd(cmd, arg1, arg2, arg3)
        print( "send_command: sending data=%s" % data)
        n = self.sock.send(data)
        # check if all data was sent
        if n < len(data):
            raise SendError
        self.request_id += 1

    def parse_response(self, data):
        try:
            match = self.response_re.match(data)
            return [self.deserialize(match.group(n)) for n in (1,2,3,4)]
        except Exception as e:
            print( "Parse error, data=%s" % data)
            raise e

    def process_response(self):
        data = self.recv_all()
        print("process_response: Response data=%s" % data)

    def read(self):
        self.send_command('READ')

    def get(self, k):
        self.send_command('GET', k)

    def get_no_wait(self, k):
        self.send_command('GET', k)

    def put_no_wait(self, k, v):
        self.send_command('PUT', k, v)

    def put(self, k, v):
        self.send_command('PUT', k, v)

    def delete(self, k):
        self.send_command('DEL', k)

    def compare_and_set(self, k, current, new):
        self.send_command('CAS', k, current, new)

    def compare_and_delete(self, k, current):
        self.send_command('CAD', k, current)

