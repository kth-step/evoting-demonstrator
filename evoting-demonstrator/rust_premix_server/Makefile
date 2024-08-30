
.PHONY: server udp tcp

UDP_ADDRESS=127.0.0.1
UDP_PORT=7879
TCP_ADDRESS=127.0.0.1:7878

server:
	env \
		UDP_ADDRESS=$(UDP_ADDRESS):$(UDP_PORT) \
		TCP_ADDRESS=$(TCP_ADDRESS) \
		cargo run --bin=inputserver

udp:
	nc -u $(UDP_ADDRESS) $(UDP_PORT)

tcp:
	curl $(TCP_ADDRESS) --output - -s | hexdump

