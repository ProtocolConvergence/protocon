
#ifndef MpiDissemNet_HH_
#define MpiDissemNet_HH_

#include <mpi.h>
#include "cx/synhax.hh"
#include "cx/table.hh"

class MpiDissemNet
{
protected:
  bool done;
  bool term;
  uint x_degree;
  uint o_degree;
  int value;
  int tag;
  MPI_Comm comm;
  Cx::Table<uint> hood;
  Cx::Table< uint > paysizes;
  Cx::Table< Cx::Table<uint> > payloads;
  Cx::Table<MPI_Request> requests;
  Cx::Table<MPI_Status > statuses;
  Cx::Table<Bool> done_flags;
  Cx::Table< Cx::Table<uint> > next_o_payloads;
  Cx::Table< int > indices;
public:
  uint PcIdx;
public:

  MpiDissemNet(uint _PcIdx, uint NPcs, int _tag, MPI_Comm _comm);

  uint x_sz() const { return x_degree; }
  uint o_sz() const { return o_degree; }
  uint xo_sz() const { return x_degree+o_degree; }

  int x_hood(uint i) { return hood[i]; }
  int o_hood(uint i) { return hood[this->x_sz() + i]; }
  uint* x_paysize(uint i) { return &paysizes[2*i]; }
  uint* o_paysize(uint i) { return &paysizes[2*(this->x_sz() + i)]; }
  Cx::Table<uint>& x_payload(uint i) { return payloads[i]; }
  Cx::Table<uint>& o_payload(uint i) { return payloads[this->x_sz() + i]; }
  MPI_Request* x_request(uint i) { return &requests[i]; }
  MPI_Request* o_request(uint i) { return &requests[this->x_sz() + i]; }
  MPI_Request* x_requests() { return this->x_request(0); }
  MPI_Request* o_requests() { return this->o_request(0); }
  MPI_Status* x_status(uint i) { return &statuses[i]; }
  MPI_Status* o_status(uint i) { return &statuses[this->x_sz() + i]; }
  MPI_Status* x_statuses() { return this->x_status(0); }
  MPI_Status* o_statuses() { return this->o_status(0); }
protected:
  Bool& x_done_flag(uint i) { return done_flags[i]; }
  Bool& o_done_flag(uint i) { return done_flags[this->x_sz() + i]; }

protected:
  void handle_recv(uint i);
  void handle_send(uint i);

public:
  void maysend();

  void terminate();
  void done_fo();
  bool done_ck();
};

#endif

