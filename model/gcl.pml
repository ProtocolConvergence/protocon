
// This is a model in progress.
// Trying to formalize a protocol which allows guarded command
// semantics and preserves stabilization.

#define N 3
#define domsz 3

typedef PcTopo {
  byte vals[N]; // My view of the world.
  bit opcs[N]; // Can read me.
  chan comm = [0] of { byte, byte };
};

PcTopo topos[N];

proctype fsm(byte pcidx)
{
  bool acting = false;
  bool waiting = false;
  byte i;
  byte val;
  select(val : 0..(domsz-1));
  topos[pcidx].vals[pcidx] = val;
  do
  :: true ->
     for (i : 0..(N-1)) {
       bool ck_xget = (i != pcidx && topos[pcidx].vals[i] < domsz);
       bool ck_oput = (i != pcidx && topos[pcidx].opcs[i] == 1);

       if
       :: ck_xget && acting ->
          assert(topos[pcidx].vals[i] == topos[i].vals[pcidx]);
       ::  ck_xget && !ck_oput && !acting -> skip;
       :: !ck_xget &&  ck_oput && !acting -> skip;
       ::  ck_xget &&  ck_oput && !acting -> skip;
       :: else -> skip;
       fi;
     }
     select(val : 0..(domsz-1));
  od;
}

init {
  byte pcidx;
  for (pcidx : 0..(N-1)) {
    byte i;
    for (i : 0..(N-1)) {
      topos[pcidx].vals[i] = domsz;
    }

    for (i : 0..(N-2)) {
      byte j;
      select(j : 0..(N-1));
      if
      :: j != pcidx ->
         topos[pcidx].vals[j] = 0;
         topos[j].opcs[pcidx] = 1;
      :: else ->
         skip;
      fi;
    }
  }
  for (pcidx : 0..(N-1)) {
    run fsm(pcidx);
  }
}

