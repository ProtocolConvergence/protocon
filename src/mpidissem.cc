
#include "mpidissem.hh"

#include "kautz.hh"

namespace Cx {

MpiDissem::MpiDissem(int _comm_tag, MPI_Comm _comm, uint degree)
  : done(false)
  , term(false)
  , comm_tag(_comm_tag)
  , comm(_comm)
{
  uint NPcs = 0;
  {
    int _PcIdx = 0;
    int _NPcs = 0;
    MPI_Comm_rank (this->comm, &_PcIdx);
    MPI_Comm_size (this->comm, &_NPcs);
    this->PcIdx = _PcIdx;
    NPcs = _NPcs;
  }

  if (NPcs <= degree) {
    for (uint i = 0; i < NPcs; ++i)  if (i != PcIdx)  hood.push(i);
    x_degree = hood.sz();
    o_degree = hood.sz();
    for (uint i = 0; i < NPcs; ++i)  if (i != PcIdx)  hood.push(i);
  }
  else {
    x_degree = gkautz_comm_hood(this->hood, PcIdx, degree, NPcs);
    o_degree = hood.sz() - x_degree;
  }

  paysizes.grow(2*this->xo_sz(), 0);
  payloads.grow(this->xo_sz());
  requests.grow(this->xo_sz(), MPI_REQUEST_NULL);
  statuses.grow(this->xo_sz());
  done_flags.grow(this->xo_sz(), 0);
  next_o_payloads.grow(this->o_sz());
  indices.grow(this->xo_sz(), -1);

  for (uint i = 0; i < this->x_sz(); ++i) {
    MPI_Irecv(this->x_paysize(i), 2, MPI_UNSIGNED,
              this->x_hood(i), this->comm_tag, this->comm,
              this->x_request(i));
  }
}

  void
MpiDissem::finish()
{
  Cx::Table<uint> msg;
  this->done_fo();

  MpiDissem::Tag tag = 0;
  while (this->xwait(tag, msg)) {
    // Nothing.
  }
}

  void
MpiDissem::reset()
{
  this->finish();
  for (uint i = 0; i < this->xo_sz(); ++i) {
    payloads[i].clear();
    requests[i] = MPI_REQUEST_NULL;
    done_flags[i] = 0;
  }
  for (uint i = 0; i < this->o_sz(); ++i) {
    next_o_payloads[i].clear();
  }

  for (uint i = 0; i < this->x_sz(); ++i) {
    MPI_Irecv(this->x_paysize(i), 2, MPI_UNSIGNED,
              this->x_hood(i), this->comm_tag, this->comm,
              this->x_request(i));
  }
}

  bool
MpiDissem::xtestlite(Tag& tag, Cx::Table<uint>& msg)
{
  for (uint i = 0; i < this->x_sz(); ++i) {
    if (*this->x_request(i) == MPI_REQUEST_NULL
        &&
        this->x_payload(i).sz() > 0)
    {
      Cx::Table<uint>& payload = this->x_payload(i);
      tag = payload.top();

      payload.cpop();
      const uint n = payload.top();

      msg.flush();
      msg.ensize(n);
      for (uint j = 0; j < n; ++j) {
        payload.cpop();
        msg[j] = payload.top();
      }
      // Use the last pop to resize in memory.
      payload.mpop();

      if (payload.sz() == 0) {
        MPI_Irecv(this->x_paysize(i), 2, MPI_UNSIGNED,
                  this->x_hood(i), this->comm_tag, this->comm,
                  this->x_request(i));
      }
      return true;
    }
    else if (*this->x_request(i) == MPI_REQUEST_NULL)
    {
      Claim2( this->x_payload(i).sz() ,==, 0 );
      Claim( this->x_done_flag(i) );
    }
  }
  return false;
}

  bool
MpiDissem::xtest(Tag& tag, Cx::Table<uint>& msg)
{
  if (this->xtestlite(tag, msg))
    return true;
  int count = 0;
  MPI_Testsome(this->xo_sz(), &this->requests[0],
               &count, &this->indices[0],
               &this->statuses[0]);
  if (count == MPI_UNDEFINED)
    return false;
  bool some_recv = false;
  for (int indices_idx = 0; indices_idx < count; ++indices_idx) {
    uint i = (uint) this->indices[indices_idx];
    if (i < this->x_sz()) {
      this->handle_recv(i);
      some_recv = true;
    }
  }
  if (some_recv) {
    return this->xtestlite(tag, msg);
  }
  return false;
}

  bool
MpiDissem::xwait(Tag& tag, Cx::Table<uint>& msg)
{
  this->maysend();
  while (!this->xtestlite(tag, msg))
  {
    int count = 0;
#if 0
    for (uint i = 0; i < this->xo_sz(); ++i) {
      DBog3("pc:%u req:%u pending:%u", PcIdx, i, this->requests[i] == MPI_REQUEST_NULL ? 0 : 1);
    }
#endif
    MPI_Waitsome(this->xo_sz(), &this->requests[0],
                 &count, &this->indices[0],
                 &this->statuses[0]);
    if (count == MPI_UNDEFINED || count == 0)
      return false;
    for (int indices_idx = 0; indices_idx < count; ++indices_idx) {
      uint i = (uint) indices[indices_idx];
      if (i < this->x_sz()) {
        /* DBog2("recv %u <- %u", PcIdx, x_hood(i)); */
        this->handle_recv(i);
      }
      else {
        this->handle_send(i-this->x_sz());
      }
    }
  }
  return true;
}

  void
MpiDissem::handle_recv(uint i)
{
  if (*this->x_request(i) != MPI_REQUEST_NULL)
    return;
  if (this->x_done_flag(i))
    return;

  if (this->x_payload(i).sz() > 0)
    return;

  uint paysize = *this->x_paysize(i);
  if (paysize > 0) {
    this->x_payload(i).grow(paysize);
    MPI_Irecv(&this->x_payload(i)[0], paysize, MPI_UNSIGNED,
              this->x_hood(i), this->comm_tag, this->comm,
              this->x_request(i));
  }
  else {
    this->x_done_flag(i) = 1;
    if (this->x_paysize(i)[1] == 0) {
      this->done_fo();
    }
    else {
      this->terminate();
    }
  }
}

  void
MpiDissem::handle_send(uint i)
{
  if (!this->o_ready(i))
    return;

  if (this->done) {
    this->o_payload(i).clear();
    this->next_o_payloads[i].clear();
    this->o_paysize(i)[0] = 0;
    this->o_paysize(i)[1] = this->term ? 1 : 0;
#if 0
    if (this->term)
      DBog2("TERM SEND %u -> %d", PcIdx, o_hood(i));
    else
      DBog2("DONE SEND %u -> %d", PcIdx, o_hood(i));
#endif
    MPI_Isend(this->o_paysize(i), 2, MPI_UNSIGNED,
              this->o_hood(i), this->comm_tag, this->comm,
              this->o_request(i));
    this->o_done_flag(i) = 1;
  }
  else if (this->next_o_payloads[i].sz() > 0) {
    // Initialize payloads.
    uint paysize = next_o_payloads[i].sz();
    this->o_paysize(i)[0] = paysize;
    this->o_paysize(i)[1] = 0;
    this->o_payload(i) = next_o_payloads[i];
    // Reverse the array, since we use it like a stack on the receiving end.
    this->o_payload(i).reverse();
    next_o_payloads[i].clear();
    // Send size.
    MPI_Isend(this->o_paysize(i), 2, MPI_UNSIGNED,
              this->o_hood(i), this->comm_tag, this->comm,
              this->o_request(i));
    MPI_Request_free(this->o_request(i));
    MPI_Isend(&this->o_payload(i)[0], paysize, MPI_UNSIGNED,
              this->o_hood(i), this->comm_tag, this->comm,
              this->o_request(i));
  }
}

  void
MpiDissem::maysend()
{
  int count = 0;
  MPI_Testsome(this->o_sz(), this->o_requests(),
               &count, &this->indices[0], this->o_statuses());

  for (uint i = 0; i < this->o_sz(); ++i) {
    this->handle_send(i);
  }
}

  void
MpiDissem::terminate()
{
  this->done = true;
  this->term = true;
}

  void
MpiDissem::done_fo()
{
  this->done = true;
}

  bool
MpiDissem::done_ck()
{
  return done;
}

} // namespace Cx

