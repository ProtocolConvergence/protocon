#!/bin/sh

proj_path=$(dirname $(dirname $(dirname "$0")))
protocon_exe="${proj_path}/../bin/protocon"

new_name="$1"
key="$2"
invariant="$3"

xfile="tmp/${key}.protocon"
ofile="${new_name}/${key}.protocon"

cat >"$xfile" <<EOF
constant N := 3;
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

"${protocon_exe}" -def N 4 -x "$xfile" -o "$ofile" -x-args search.args \
1>/dev/null 2>&1

retcode=$?

#1>tmp/${key}.log 2>&1

if [ $retcode -eq 0 ]
then
  echo $key success
else
  echo $key failure
fi

rm -f "$xfile"

