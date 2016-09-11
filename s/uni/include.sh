
proj_path=$(dirname $(dirname "${this_exe_path}"))
classify_exe="${proj_path}/bld/uni/classify"
gen_exe="${proj_path}/bld/uni/generate"
xlate_exe="${proj_path}/bld/uni/xlate"

function calc_domsz()
{
  local domsz btsz
  domsz=2
  btsz=$(printf '%s' "$1" | wc -c)
  while [ $(($domsz * $domsz * $domsz)) -lt $btsz ]
  do
    domsz=$(($domsz + 1))
  done
  printf '%s' $domsz
}

