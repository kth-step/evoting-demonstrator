
# file: etc/init.d/S60confnet.sh
#
# automatically configure eth0
ifconfig eth0 192.100.1.2 netmask 255.255.255.0

# automatically configure the gateway
route add default gw 192.100.1.1 eth0

echo "nameserver 193.10.64.9" > /etc/resolv.conf

