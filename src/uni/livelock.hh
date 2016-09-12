#ifndef UNI_LIVELOCK_HH_
#define UNI_LIVELOCK_HH_

#define each_in_BitTable(i , bt) \
  (zuint i = bt.begidx(); i < bt.sz(); bt.nextidx(&i))

#include "uniact.hh"

#include "../namespace.hh"
template <typename T> class AdjList;

void
subtract_action_mask(BitTable& mask, const UniAct& mask_act, uint domsz);
bool
action_mask_overlap_ck(const UniAct& mask_act,
                       const BitTable& actset, uint domsz);
Trit
livelock_semick(const uint limit,
                Table<PcState> ppgfun,
                const uint domsz,
                Table<PcState>* ret_row=0,
                Table<PcState>* ret_col=0);
bool
guided_livelock_ck(const Table< Tuple<uint,2> >& acts,
                   const Table<PcState>& ppgfun,
                   const uint domsz,
                   BitTable& livelockset,
                   const uint limit);
bool
cycle_ck_from(uint initial_node, const AdjList<uint>& digraph,
              Table< Tuple<uint,2> >& stack,
              BitTable& visited);
void
make_tile_cont_digraph(AdjList<uint>& digraph, const BitTable& actset,
                       const Table<PcState>& ppgfun, const uint domsz);
void
make_overapprox_tile_cont_digraph(AdjList<uint>& digraph,
                                  const BitTable& actset,
                                  const uint domsz);
END_NAMESPACE
#endif
