
#include "mpidissem.hh"

static
  int
egcd(int* ret_a, int* ret_b)
{
  int a = *ret_a;
  int b = *ret_b;
  int x = 0;
  int y = 1;
  int u = 1;
  int v = 0;
  while (a != 0) {
    int q = b / a;
    int r = b % a;
    b = a;
    a = r;
    int m = x - u * q;
    x = u;
    u = m;
    int n = y - v * q;
    y = v;
    v = n;
  }
  *ret_a = x;
  *ret_b = y;
  return b;
}

/**
 * a x % n = b
 */
static
  void
linear_congruence(Cx::Table<uint>& ans, uint a, uint n, uint b)
{
  int r = a,
      s = n;
  uint d = umod_int(egcd(&r, &s), n);
  uint n_div_d = n / d;
  if (0 != b % d)  return;
  uint x0 = umod_int(r * (int) b / (int)d, n);
  for (uint i = 0; i < d; ++i) {
    ans.push((x0 + i * n_div_d) % n);
  }
}

/**
 * Generalized Kautz graph topology of degree {degree}.
 * The {hood} parameter is filled by 2*{degree} nodes.
 * The first {degree} nodes are sources for arcs whose destination node is {vidx}.
 * The second {degree} nodes are destinations for arcs whose source node is {vidx}.
 */
static
  void
gkautz_hood(Cx::Table<uint>& hood, uint vidx, uint degree, uint n)
{
  // For arcs ending at node {vidx}, solve the following
  //   -(vidx + q) % n = i * degree % n
  // for
  //   q <- {1,...,degree}
  // to obtain each source node {i}.
  // Depending on {degree} and {n}, a single {q} may generate zero or multiple solutions,
  // but there are exactly {degree} solutions in total.
  for (uint q = 1; q <= degree; ++q) {
    Cx::Table<uint> ans;
    linear_congruence
      (ans, degree, n,
       umod_int (- (int)(vidx + q), n)
      );
    for (uint i = 0; i < ans.sz(); ++i) {
      hood.push(ans[i]);
      //DBog3("%0.2u %0.2u %u", ans[i], vidx, q);
    }
  }
  Claim2( hood.sz() ,==, degree );

  // For arcs beginning at node {vidx}, solve the following
  //   j = -(vidx * degree + q) % n
  // for
  //   q <- {1,...,degree}
  // to obtain each destination node {j}.
  // Each q gives a unique {j}.
  for (uint q = 1; q <= degree; ++q) {
    uint j = umod_int (-(int)(vidx * degree + q), n);
    hood.push(j);
    //DBog3("%0.2u %0.2u %u", vidx, j, q);
  }
  Claim2( hood.sz() ,==, 2*degree );
}

/**
 * Generalized Kautz graph topology of degree {degree}.
 * The {hood} parameter is filled by {x_degree}+{o_degree} nodes.
 * The first {x_degree} nodes are sources for arcs whose destination node is {vidx},
 * excluding {vidx} and duplicate source nodes.
 * The second {o_degree} nodes are destinations for arcs whose source node is {vidx},
 * excluding {vidx} and duplicate destination nodes.
 *
 * \return  The indegree {x_degree} of this node.
 */
static
  uint
gkautz_comm_hood(Cx::Table<uint>& hood, uint vidx, uint degree, uint n)
{
  gkautz_hood(hood, vidx, degree, n);
  uint x_degree;
  uint off = 0;
  for (uint i = 0; i < degree; ++i) {
    bool found = (vidx == hood[i]);
    for (uint j = 0; j < off && !found; ++j) {
      if (hood[j] == hood[i])
        found = true;
    }
    if (!found)
      hood[off++] = hood[i];
  }
  x_degree = off;
  for (uint i = degree; i < 2*degree; ++i) {
    bool found = (vidx == hood[i]);
    for (uint j = x_degree; j < off && !found; ++j) {
      if (hood[j] == hood[i])
        found = true;
    }
    if (!found)
      hood[off++] = hood[i];
  }
  if (hood.sz() != off) {
    hood.resize(off);
  }
  return x_degree;
}


MpiDissem::MpiDissem(uint _PcIdx, uint NPcs, int _tag, MPI_Comm _comm)
  : done(false)
  , term(false)
  , value(-1)
  , tag(_tag)
  , comm(_comm)
  , PcIdx(_PcIdx)
{
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

