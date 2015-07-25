#!/bin/sh

proj_path=$(dirname $(dirname $(dirname "$0")))
protocon_exe="${proj_path}/bin/protocon"

old_name="$1"
new_name="$2"
key="$3"
invariant="$4"

xtryfile="${old_name}/${key}.protocon"
xfile="tmp/pid$PPID-${key}.protocon"
ofile="${new_name}/${key}.protocon"

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

"$protocon_exe" -def N 4 -x "$xfile" -o "$ofile" -x-try "$xtryfile" -x-args opt.args \
1>/dev/null 2>&1

retcode=$?

#1>"log/${key}.log" 2>&1

if [ $retcode -eq 0 ]
then
  echo "$key" success
  #rm -f log/${key}.tlog
else
  echo "$key" failure
  #cp -f "$xfile" "log/${key}.protocon"
fi

rm -f "$xfile"

