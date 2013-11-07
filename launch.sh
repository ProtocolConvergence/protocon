#!/bin/sh

args_file=args

#npcs=21
npcs=88
#npcs=10
#npcs=42

mode=""
mode="-minimize-conflicts"
#mode="-minimize-conflicts-lohi"
#mode="-verify"
misc=""
#misc="-try-all"

path=kautz14
xspec="-x inst/ColorKautz.protocon"
ospec=""
if false
then
  PrevN=13
  InstN=14
  xspec="$xspec -x-list $path/v${PrevN}.protocon.* ."
  ospec="-o $path/v${InstN}.protocon"
  xconflicts="-x-conflicts $path/v${PrevN}.conflicts"
  oconflicts="-o-conflicts $path/v${InstN}.conflicts"
  olog="-o-log $path/v${InstN}.log"
else
  ospec="-o $path/min.protocon"
  xconflicts="-x-conflicts $path/min.conflicts"
  oconflicts="-o-conflicts $path/min.conflicts"
  olog="-o-log $path/min.log"
fi

params="-def N 3"
#params="-def N 4"
#params="$params -param N 3"
params="$params -param N 5"
params="$params -param N 4"
params="$params -param N 6"
params="$params -param N 7"
params="$params -param N 8"
params="$params -param N 9"
#params="$params -param N 10"
#params="$params -param N 11"
#params="$params -param [ -def N 11 -no-conflict ]"
#params="$params -param [ -def N 10 -no-conflict ]"
#params="$params -param [ -def N 13 -no-conflict ]"
#params="$params -param [ -def N 14 -no-conflict ]"
#params="-def N ${InstN}"

pick=""
#pick="-pick fully-random"
pick="-pick-reach"

trials=""
trials="$trials -try-all"
#trials="$trials -ntrials 2"

if [ "$mode" = "-minimize-conflicts" \
  -o "$mode" = "-minimize-conflicts-lohi" \
  -o "$mode" = "-verify" ]
then
  if [ "$mode" != "-verify" ]
  then
    ospec=""
  fi
  pick=""
  trials=""
fi

args="$mode $xspec $ospec $misc $pick $trials $params $xconflicts $oconflicts $olog"
echo $args > "$args_file"

cmd="mpirun -q 0 -np $npcs -stdin '$args_file'"
#cmd="$cmd ../bin/protocon-mpi $args"
cmd="$cmd ../bin/protocon-mpi -x-args /dev/stdin"

echo "$cmd"
echo args: $args
exec $cmd

