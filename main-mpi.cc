
extern "C" {
#include "cx/syscx.h"
}
#include <mpi.h>

int main(int argc, char** argv)
{
  MPI_Init (&argc, &argv);
  int argi = (init_sysCx (&argc, &argv), 1);
  (void) argi;
  push_losefn_sysCx ((void (*) ()) MPI_Finalize);
  uint PcIdx = 0;
  uint NPcs = 1;
  MPI_Comm_rank (MPI_COMM_WORLD, (int*) &PcIdx);
  MPI_Comm_size (MPI_COMM_WORLD, (int*) &NPcs);
  fprintf(stderr, "Hello from %u / %u!\n", PcIdx, NPcs);
  MPI_Barrier (MPI_COMM_WORLD);
  fprintf(stderr, "Wah! from %u / %u!\n", PcIdx, NPcs);
  lose_sysCx ();
  return 0;
}

