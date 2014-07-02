
#include "mpidissem.hh"

MpiDissem::MpiDissem(uint _PcIdx, uint NPcs, int _tag, MPI_Comm _comm)
  : MpiDissemNet(_PcIdx, NPcs, _tag, _comm)
{
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

