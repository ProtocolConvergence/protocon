#!/bin/sh

cd $(dirname "$0")

old_pathpfx="$1"
new_pathpfx="$2"
key="$3"
invariant="$4"

xtryfile="$old_pathpfx/$key.protocon"
xfile="tmp/pid$PPID-$key.protocon"
ofile="$new_pathpfx/$key.protocon"

cat >"$xfile" <<EOF
constant N := 4;
constant M := 3;
variable x[Nat % N] <- Nat % M;
process P[i <- Nat % N]
{
write: x[i];
read: x[i-1];
read: x[i+1];
invariant:
$invariant
;
}
EOF

../../bin/protocon -def N 4 -x "$xfile" -o "$ofile" -x-try "$xtryfile" \
  -x-args optargs 1>/dev/null 2>&1

  #-x-args optargs 1>"log/$key.log" 2>&1

if [ $? -eq 0 ]
then
  echo "$key" success
  #rm -f log/$key.tlog
else
  echo "$key" failure
  #cp -f "$xfile" "log/$key.protocon"
fi

rm -f "$xfile"

