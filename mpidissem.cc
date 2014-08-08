
#include "mpidissem.hh"

#include "kautz.hh"

MpiDissem::MpiDissem(int _tag, MPI_Comm _comm)
  : done(false)
  , term(false)
  , value(-1)
  , tag(_tag)
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

  const uint degree = 4;
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
              this->x_hood(i), this->tag, this->comm,
              this->x_request(i));
  }
}

  bool
MpiDissem::xtestlite(Cx::Table<uint>& ret)
{
  for (uint i = 0; i < this->x_sz(); ++i) {
    if (*this->x_request(i) == MPI_REQUEST_NULL) {
      if (this->x_payload(i).sz() > 0) {
        ret = this->x_payload(i);
        this->x_payload(i).flush();
        MPI_Irecv(this->x_paysize(i), 2, MPI_UNSIGNED,
                  this->x_hood(i), this->tag, this->comm,
                  this->x_request(i));
        return true;
      }
      else {
        Claim( this->x_done_flag(i) );
      }
    }
  }
  return false;
}

  bool
MpiDissem::xtest(Cx::Table<uint>& ret)
{
  if (this->xtestlite(ret))
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
    this->xtestlite(ret);
    return true;
  }
  return false;
}

  bool
MpiDissem::xwait(Cx::Table<uint>& ret)
{
  this->maysend();
  while (!this->xtestlite(ret))
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
              this->x_hood(i), this->tag, this->comm,
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
  if (*this->o_request(i) != MPI_REQUEST_NULL)
    return;
  if (this->o_done_flag(i))
    return;

  if (this->next_o_payloads[i].sz() > 0) {
    // Initialize payloads.
    uint paysize = next_o_payloads[i].sz();
    this->o_paysize(i)[0] = paysize;
    this->o_paysize(i)[1] = 0;
    this->o_payload(i) = next_o_payloads[i];
    next_o_payloads[i].clear();
    // Send size.
    MPI_Isend(this->o_paysize(i), 2, MPI_UNSIGNED,
              this->o_hood(i), this->tag, this->comm,
              this->o_request(i));
    MPI_Request_free(this->o_request(i));
    MPI_Isend(&this->o_payload(i)[0], paysize, MPI_UNSIGNED,
              this->o_hood(i), this->tag, this->comm,
              this->o_request(i));
  }
  else if (this->done) {
    this->o_paysize(i)[0] = 0;
    this->o_paysize(i)[1] = this->term ? 1 : 0;
#if 0
    if (this->term)
      DBog2("TERM SEND %u -> %d", PcIdx, o_hood(i));
    else
      DBog2("DONE SEND %u -> %d", PcIdx, o_hood(i));
#endif
    MPI_Isend(this->o_paysize(i), 2, MPI_UNSIGNED,
              this->o_hood(i), this->tag, this->comm,
              this->o_request(i));
    this->o_done_flag(i) = 1;
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

