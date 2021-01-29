
#ifndef MpiDissem_HH_
#define MpiDissem_HH_

#include <mpi.h>
#include "cx/synhax.hh"
#include "cx/table.hh"

namespace Cx {
class MpiDissem
{
private:
  bool done;
  bool term;
  uint x_degree;
  uint o_degree;
public:
  uint PcIdx;
  typedef uint Tag;
  Tag comm_tag;
private:
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
  MpiDissem(int _comm_tag, MPI_Comm _comm, uint degree=4);

  void finish();
  void reset();

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

  bool xtestlite(Tag& tag, Cx::Table<uint>& msg);
  bool xtest(Tag& tag, Cx::Table<uint>& msg);
  bool xwait(Tag& tag, Cx::Table<uint>& msg);

private:
  Bool& x_done_flag(uint i) { return done_flags[i]; }
  Bool& o_done_flag(uint i) { return done_flags[this->x_sz() + i]; }

  void handle_recv(uint i);
  void handle_send(uint i);

public:
  bool o_ready(uint i) {
    return !this->o_done_flag(i) && (*this->o_request(i) == MPI_REQUEST_NULL);
  }

  void maysend();

  void terminate();
  void done_fo();
  bool done_ck();

  void pushto(uint i, Tag tag, const Cx::Table<uint>& msg)
  {
    if (this->done)  return;
    this->next_o_payloads[i].push(tag);
    this->next_o_payloads[i].push(msg.sz());
    for (uint j = 0; j < msg.sz(); ++j)
      this->next_o_payloads[i].push(msg[j]);
  }

  void push(Tag tag, const Cx::Table<uint>& msg)
  {
    if (this->done)  return;
    for (uint i = 0; i < this->o_sz(); ++i)
      this->pushto(i, tag, msg);
  }
};
}

#endif

