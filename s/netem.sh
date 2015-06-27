
# Source this as root.

# Example commands:
cat >/dev/null <<'EOF'
# Initialize.
init_iface
init_netem

# Teardown.
lose_netem
lose_iface

# Connection settings.
set_netem corrupt 50%
set_netem delay 500ms
set_netem duplicate 50%
set_netem delay 500ms 500ms
set_netem loss 50%

# Run as a normal user to capture traffic.
wireshark -k -i lo -f "host 10.0.0.1"
EOF


### Virtual Network Interface ###
# Using TUN/TAP to make virtual network interface.
real_iface=tap0
iface=lo
ipaddr=10.0.0.1

function init_iface()
{
  ip tuntap add dev $real_iface mode tap
  ip addr add $ipaddr/24 dev $real_iface
  ip link set $real_iface up
}

function lose_iface()
{
  ip tuntap del dev $real_iface mode tap
}

### NETEM Filter by IP ###

function init_netem()
{
  tcid_base="dev $iface root handle 1: prio"
  tcid_filter="dev $iface protocol ip parent 1: prio 1"
  tcid_netem="dev $iface parent 1:1 handle 10:"
  tc qdisc add $tcid_base
  tc filter add $tcid_filter u32 match ip src $ipaddr flowid 1:1
  tc qdisc add $tcid_netem netem delay 0
}

function lose_netem()
{
  tc filter del $tcid_filter
  tc qdisc del $tcid_netem
  tc qdisc del $tcid_base
}

function show_netem()
{
  tc qdisc show dev $iface \
  | grep -m 1 -e netem \
  | grep -o -e 'limit.*$' \
  | cat
}

function set_netem()
{
  tc qdisc change $tcid_netem netem $(show_netem) "$@"
  show_netem
}

function wipe_netem()
{
  tc qdisc change $tcid_netem netem delay 0 corrupt 0
  show_netem
}

function eq ()
{
  return $(expr + "$1" != + "$2")
}

function empty_ck ()
{
  eq "" "$1"
  return $?
}

