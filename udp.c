
#include "cx/def.h"
#include <stdint.h>
#include <sys/types.h>
#include <netdb.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include <poll.h>
#include <signal.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdio.h>

typedef struct Packet Packet;
typedef struct Channel Channel;
typedef struct State State;

struct Packet
{
  uint32_t src_seq;
  uint32_t dst_seq;
  uint32_t enabled;
  uint32_t state;
};

struct Channel
{
  uint32_t seq;
  uint32_t adj_seq;
  struct sockaddr_in host;
  uint adj_PcIdx;
  //uint32_t adj_enabled;
  Bool acknowledged;
};

struct State
{
  int fd;
  int urandom_fd;
  uint32_t enabled;
  uint32_t x_lo;
  uint32_t x_me;
  uint32_t x_hi;
  uint PcIdx;
  uint NPcs;
  Channel channels[2];
};

static const char SharedFilePfx[] = "udp-host.";
static const Bool ShowCommunication = 0;

#define BailOut( ret, msg ) \
do \
{ \
  failmsg(msg); \
  return ret; \
} while (0)

void failmsg(const char* msg)
{
  if (errno != 0) {
    perror(msg);
  }
  else {
    fprintf(stderr, "%s\n", msg);
  }
}

  void
hton_Packet (Packet* pkt)
{
  pkt->src_seq = htonl (pkt->src_seq);
  pkt->dst_seq = htonl (pkt->dst_seq);
  pkt->enabled = htonl (pkt->enabled);
  pkt->state = htonl (pkt->state);
}

  void
ntoh_Packet (Packet* pkt)
{
  pkt->src_seq = ntohl (pkt->src_seq);
  pkt->dst_seq = ntohl (pkt->dst_seq);
  pkt->enabled = ntohl (pkt->enabled);
  pkt->state = ntohl (pkt->state);
}

  int
next_urandom(uint32_t* x, State* st)
{
  int stat;
  stat = read(st->urandom_fd, x, sizeof(*x));
  if (stat != sizeof(*x))
    BailOut(-1, "next_urandom() -- read()");
  return 0;
}

  void
next_seq(Channel* channel, State* st)
{
  uint32_t* seq = &channel->seq;
  uint32_t x = 0;
  next_urandom(&x, st);
  x |= 0x0000FFFF;
  *seq += 1;
  *seq |= 0xFFFF0000;
  *seq &= x;
}

  void
CMD_enable(State* st)
{
  next_urandom(&st->enabled, st);
  st->enabled |= 0x80000000;
  for (uint i = 0; i < 2; ++i) {
    next_seq(&st->channels[i], st);
    st->channels[i].acknowledged = 0;
  }
}

  void
CMD_disable(State* st)
{
  st->enabled = 0;
  for (uint i = 0; i < 2; ++i) {
    next_seq(&st->channels[i], st);
  }
}

  int
lookup_host(struct sockaddr_in* host, uint id)
{
  int port;
  char hostname[128];
  char fname[128];
  FILE* f;
  int nmatched;
  sprintf(fname, "%s%d", SharedFilePfx, id);
  f = fopen(fname, "rb");
  if (!f) {
#ifdef DebugLogging
    BailOut(-1, "fopen()");
#else
    return -1;
#endif
  }
  nmatched = fscanf(f, "%128s %d", hostname, &port);
  if (nmatched < 2)
    BailOut(-1, "fscanf()");
  fclose(f);

  {
    struct hostent* ent;
    ent = gethostbyname(hostname);
    if (!ent)
      BailOut(-1, "gethostbyname()");

    memset(host, 0, sizeof(host));
    host->sin_family = AF_INET;
    memcpy(&host->sin_addr, ent->h_addr, ent->h_length);
    host->sin_port = htons(port);
  }
  return 0;
}

  void
init_Channel(Channel* channel, State* st)
{
  channel->seq = 0;
  next_seq(channel, st);
  channel->adj_seq = 0;
  channel->acknowledged = 0;
  memset(&channel->host, 0, sizeof(channel->host));
  {
    uint id;
    if (channel == &st->channels[0])
      id = (st->PcIdx + st->NPcs - 1) % st->NPcs;
    else
      id = (st->PcIdx + 1) % st->NPcs;
    channel->adj_PcIdx = id;
    while (0 > lookup_host(&channel->host, id)) {
      sleep(1);
    }
  }
}

  void
randomize_State(State* st)
{
  next_urandom(&st->x_lo, st);
  next_urandom(&st->x_me, st);
  next_urandom(&st->x_hi, st);
  next_urandom(&st->enabled, st);
  for (uint i = 0; i < 2; ++i) {
    uint32_t tmp;
    Channel* channel = &st->channels[i];
    next_urandom(&channel->seq, st);
    next_urandom(&channel->adj_seq, st);
    next_urandom(&tmp, st);
    channel->acknowledged = tmp % 2;
  }
}

  int
init_State(State* st, uint PcIdx, uint NPcs)
{
  struct sockaddr_in host[1];
  memset(st, 0, sizeof(*st));
  st->urandom_fd = open("/dev/urandom", O_RDONLY);
  st->PcIdx = PcIdx;
  st->NPcs = NPcs;

  //next_urandom(&st->x_lo, st);
  //next_urandom(&st->x_hi, st);
  //do {
  //  next_urandom(&st->x_me, st);
  //  st->x_me &= 0x3;
  //} while (st->x_me >= 3);

  st->fd = socket(AF_INET, SOCK_DGRAM, 0);
  memset (host, 0, sizeof (*host));
  host->sin_family = AF_INET;
  host->sin_addr.s_addr = INADDR_ANY;
  host->sin_port = 0;
  if (0 > bind(st->fd, (struct sockaddr *)host, sizeof(*host)))
    BailOut(-1, "bind()");

  /* Fill in the host address and port.*/
  socklen_t sz = sizeof(*host);
  if (0 > getsockname(st->fd, (struct sockaddr*)host, &sz))
    BailOut(-1, "getsockname()");

  /* Write this process's host info to a file assumed to be shared on NFS.*/
  {
    char hostname[128];
    char fname[128];
    FILE* f;
    if (0 > gethostname(hostname, sizeof(hostname)))
      BailOut(-1, "gethostname()");
    sprintf(fname, "%s%d", SharedFilePfx, st->PcIdx);
    f = fopen(fname, "wb");
    if (!f)
      BailOut(-1, "fopen()");

    fprintf(f, "%s\n%d", hostname, ntohs(host->sin_port)),
    fclose(f);
  }
  init_Channel(&st->channels[0], st);
  init_Channel(&st->channels[1], st);
  randomize_State(st);
  return 0;
}

  void
lose_State(State* st)
{
  char fname[128];
  sprintf(fname, "%s%d", SharedFilePfx, st->PcIdx);
  remove(fname);
  close(st->urandom_fd);
}


  int
send_Packet (const Packet* packet, const struct sockaddr_in* host, const State* st)
{
  Packet pkt[1];
  int stat;
  *pkt = *packet;
  if (ShowCommunication)
  fprintf(stderr, "%2u -> %2u  (%u %u %u)  src_seq:%08x  dst_seq:%08x  enabled:%08x  state:%u\n",
          st->PcIdx,
          ((&st->channels[0].host == host)
           ? st->channels[0].adj_PcIdx
           : st->channels[1].adj_PcIdx),
          st->x_lo, st->x_me, st->x_hi,
          pkt->src_seq,
          pkt->dst_seq,
          pkt->enabled,
          pkt->state);
  hton_Packet(pkt);
  stat = sendto(st->fd, pkt, sizeof(*pkt), 0,
                (struct sockaddr*)host, sizeof(*host));
  return stat;
}

  Channel*
recv_Packet (Packet* pkt, State* st)
{
  int cc;
  struct sockaddr_in host[1];
  socklen_t sz = sizeof(*host);
  memset (host, 0, sz);
  cc = recvfrom(st->fd, pkt, sizeof(*pkt), 0, (struct sockaddr*)host, &sz);
  if (cc != sizeof(*pkt)) {
    BailOut(0, "recvfrom()");
  }
  ntoh_Packet(pkt);

  for (uint i = 0; i < 2; ++i) {
    Channel* channel = &st->channels[i];
    if (channel->host.sin_addr.s_addr == host->sin_addr.s_addr &&
        channel->host.sin_port == host->sin_port)
    {
      if (ShowCommunication)
      fprintf(stderr, "%2u <- %2u  (%u %u %u)  src_seq:%08x  dst_seq:%08x  enabled:%08x  state:%u\n",
              st->PcIdx,
              channel->adj_PcIdx,
              st->x_lo, st->x_me, st->x_hi,
              pkt->src_seq,
              pkt->dst_seq,
              pkt->enabled,
              pkt->state);
      return channel;
    }
  }

  BailOut(0, "who sent the message?");
}

#if 0
  void
action_assign(uint32_t* c, uint PcIdx)
{
  // 3-coloring
  const uint i = 1;
  (void) PcIdx;
  if (c[i] >= 3)  c[i] %= 3;
  while (c[i-1] == c[i] || c[i] == c[i+1]) {
    c[i] += 1;
    c[i] %= 3;
  }
}
  void
action_pre_assign(uint32_t* x, uint PcIdx)
{
  (void) x;
  (void) PcIdx;
}
#elif 0
  void
action_assign(uint32_t* x, uint PcIdx)
{
  // Matching
  const uint i = 1;
  (void) PcIdx;
  if (x[i] >= 3)  x[i] %= 3;
  if (x[i-1]==1 && x[i]!=0 && x[i+1]==2)  x[i]=0;
  if (x[i-1]!=1 && x[i]==0 && x[i+1]!=2)  x[i]=2;
  if (x[i-1]!=1 && x[i]!=1 && x[i+1]==2)  x[i]=1;
  if (x[i-1]==1 && x[i]!=2 && x[i+1]!=2)  x[i]=2;
}
  void
action_pre_assign(uint32_t* x, uint PcIdx)
{
  (void) x;
  (void) PcIdx;
}
#elif 1
  void
action_assign(uint32_t* x, uint PcIdx)
{
  const Bool GoudaAndHaddixVersion = 1;
  const uint i = 1;
  uint32_t e[2];
  uint32_t t[2];
  uint32_t ready[2];
  (void) PcIdx;

  e[i-1]   = (x[i-1] >> 2) & 1;
  e[i]     = (x[i]   >> 2) & 1;
  t[i-1]   = (x[i-1] >> 1) & 1;
  t[i]     = (x[i]   >> 1) & 1;
  ready[i] = (x[i]       ) & 1;

  if (GoudaAndHaddixVersion) {
    if (PcIdx == 0) {
      if (e[i-1] == e[i] && t[i-1] != t[i]) {
        e[i] = 1-e[i-1];
        ready[i] = 0;
      }
      if (e[i-1] == e[i] && t[i-1] == t[i] && !(t[i] == 1 || ready[i] == 1)) {
        e[i] = 1-e[i-1];
        ready[i] = 1;
      }
      if (e[i-1] == e[i] && t[i-1] == t[i] &&  (t[i] == 1 || ready[i] == 1)) {
        e[i] = 1-e[i-1];
        t[i] = 1-t[i-1];
        ready[i] = 0;
      }
    }
    else {
      if (e[i-1] != e[i] && t[i-1] == t[i]) {
        e[i] = e[i-1];
        ready[i] = 0;
      }
      if (e[i-1] != e[i] && t[i-1] != t[i] && !(t[i] == 1 || ready[i] == 1)) {
        e[i] = e[i-1];
        ready[i] = 1;
      }
      if (e[i-1] != e[i] && t[i-1] != t[i] &&  (t[i] == 1 || ready[i] == 1)) {
        e[i] = e[i-1];
        t[i] = t[i-1];
        ready[i] = 0;
      }
    }
  }
  else {
    if (PcIdx == 0) {
      if (e[i-1]==1 && t[i-1]==0 && e[i]==1 && t[i]==0 && ready[i]==0) { e[i]=0; t[i]=0; ready[i]=0; }
      if (e[i-1]==1 && t[i-1]==0 && e[i]==1 && t[i]==0 && ready[i]==1) { e[i]=0; t[i]=0; ready[i]=1; }
      if (e[i-1]==0 && t[i-1]==0 && e[i]==0 && t[i]==0 && ready[i]==1) { e[i]=1; t[i]=0; ready[i]=0; }
      if (e[i-1]==0 && t[i-1]==0 && e[i]==0 && t[i]==0 && ready[i]==0) { e[i]=0; t[i]=1; ready[i]=1; }
      if (e[i-1]==1 && t[i-1]==1 && e[i]==0 && t[i]==0 && ready[i]==1) { e[i]=1; t[i]=0; ready[i]=0; }
      if (e[i-1]==1 && t[i-1]==1 && e[i]==0 && t[i]==0 && ready[i]==0) { e[i]=1; t[i]=0; ready[i]=1; }
      if (e[i-1]==1 && t[i-1]==1 && e[i]==1 && t[i]==1 && ready[i]==1) { e[i]=0; t[i]=1; ready[i]=1; }
      if (e[i-1]==1 && t[i-1]==1 && e[i]==1 && t[i]==1 && ready[i]==0) { e[i]=0; t[i]=1; ready[i]=1; }
      if (e[i-1]==1 && t[i-1]==0 && e[i]==0 && t[i]==1 && ready[i]==1) { e[i]=1; t[i]=1; ready[i]=1; }
      if (e[i-1]==1 && t[i-1]==0 && e[i]==0 && t[i]==1 && ready[i]==0) { e[i]=1; t[i]=1; ready[i]=0; }
      if (e[i-1]==0 && t[i-1]==0 && e[i]==1 && t[i]==1 && ready[i]==1) { e[i]=0; t[i]=1; ready[i]=1; }
      if (e[i-1]==0 && t[i-1]==0 && e[i]==1 && t[i]==1 && ready[i]==0) { e[i]=0; t[i]=1; ready[i]=1; }
      if (e[i-1]==0 && t[i-1]==1 && e[i]==0 && t[i]==1 && ready[i]==1) { e[i]=0; t[i]=0; ready[i]=1; }
      if (e[i-1]==0 && t[i-1]==1 && e[i]==0 && t[i]==1 && ready[i]==0) { e[i]=1; t[i]=1; ready[i]=1; }
    }
    else {
      if (e[i-1]==1 && t[i-1]==1 && e[i]==1 && t[i]==1 && ready[i]==1) { e[i]=1; t[i]=1; ready[i]=0; }
      if (e[i-1]==1 && t[i-1]==1 && e[i]==0 && t[i]==1 && ready[i]==1) { e[i]=1; t[i]=1; ready[i]=0; }
      if (e[i-1]==1 && t[i-1]==1 && e[i]==0 && t[i]==1 && ready[i]==0) { e[i]=1; t[i]=1; ready[i]=0; }
      if (e[i-1]==1 && t[i-1]==1 && e[i]==1 && t[i]==0 && ready[i]==0) { e[i]=0; t[i]=0; ready[i]=0; }
      if (e[i-1]==0 && t[i-1]==1 && e[i]==1 && t[i]==1 && ready[i]==0) { e[i]=0; t[i]=1; ready[i]=0; }
      if (e[i-1]==0 && t[i-1]==1 && e[i]==1 && t[i]==1 && ready[i]==1) { e[i]=0; t[i]=1; ready[i]=0; }
      if (e[i-1]==0 && t[i-1]==1 && e[i]==0 && t[i]==0 && ready[i]==1) { e[i]=1; t[i]=0; ready[i]=0; }
      if (e[i-1]==1 && t[i-1]==0 && e[i]==0 && t[i]==0 && ready[i]==0) { e[i]=1; t[i]=0; ready[i]=0; }
      if (e[i-1]==1 && t[i-1]==0 && e[i]==0 && t[i]==0 && ready[i]==1) { e[i]=1; t[i]=0; ready[i]=1; }
      if (e[i-1]==1 && t[i-1]==1 && e[i]==1 && t[i]==0 && ready[i]==1) { e[i]=0; t[i]=0; ready[i]=1; }
      if (e[i-1]==0 && t[i-1]==0 && e[i]==1 && t[i]==0 && ready[i]==1) { e[i]=0; t[i]=0; ready[i]=1; }
      if (e[i-1]==0 && t[i-1]==0 && e[i]==1 && t[i]==0 && ready[i]==0) { e[i]=0; t[i]=0; ready[i]=0; }
      if (e[i-1]==0 && t[i-1]==1 && e[i]==0 && t[i]==0 && ready[i]==0) { e[i]=0; t[i]=1; ready[i]=0; }
      if (e[i-1]==0 && t[i-1]==0 && e[i]==0 && t[i]==1 && ready[i]==0) { e[i]=0; t[i]=0; ready[i]=1; }
      if (e[i-1]==0 && t[i-1]==0 && e[i]==0 && t[i]==1 && ready[i]==1) { e[i]=0; t[i]=0; ready[i]=0; }
      if (e[i-1]==1 && t[i-1]==0 && e[i]==1 && t[i]==1 && ready[i]==0) { e[i]=1; t[i]=0; ready[i]=0; }
      if (e[i-1]==1 && t[i-1]==0 && e[i]==1 && t[i]==1 && ready[i]==1) { e[i]=1; t[i]=0; ready[i]=0; }
      if (e[i-1]==1 && t[i-1]==0 && e[i]==0 && t[i]==1 && ready[i]==1) { e[i]=1; t[i]=0; ready[i]=0; }
      if (e[i-1]==1 && t[i-1]==0 && e[i]==0 && t[i]==1 && ready[i]==0) { e[i]=1; t[i]=0; ready[i]=1; }
      if (e[i-1]==0 && t[i-1]==0 && e[i]==1 && t[i]==1 && ready[i]==0) { e[i]=1; t[i]=1; ready[i]=1; }
    }
  }
  x[i] = (e[i] << 2) | (t[i] << 1) | ready[i];
}
  void
action_pre_assign(uint32_t* x, uint PcIdx)
{
  if ((PcIdx == 0 && (x[0] & 2) == (x[1] & 2))
      ||
      (PcIdx != 0 && (x[0] & 2) != (x[1] & 2)))
  {
    if (false) {
      FILE* f = fopen("shared-resource", "ab");
      fprintf(f, "%u\n", PcIdx);
      fclose(f);
    }
    fprintf(stderr, "%u WRITING TO SHARED RESOURCE\n", PcIdx);
  }
}
#endif

  Bool
smem_act(State* st, Bool modify)
{
  const uint i = 1;
  uint32_t x[3];
  x[i-1] = st->x_lo;
  x[i] = st->x_me;
  x[i+1] = st->x_hi;

  action_assign(x, st->PcIdx);

  if (x[i] != st->x_me) {
    if (modify) {

      {
        uint32_t tmp[3];
        tmp[i-1] = st->x_lo;
        tmp[i] = st->x_me;
        tmp[i+1] = st->x_hi;
        action_pre_assign(tmp, st->PcIdx);
      }

      // This helps the scheduler find livelocks.
      usleep(10000);
      if (true)
      fprintf(stderr, "%2u  ACT:  x[%u]==%u && x[%u]==%u && x[%u]==%u --> x[%u]:=%u;\n",
              st->PcIdx,
              st->channels[0].adj_PcIdx, x[i-1],
              st->PcIdx, st->x_me,
              st->channels[1].adj_PcIdx, x[i+1],
              st->PcIdx, x[i]);
      st->x_me = x[i];
    }
    return 1;
  }
  return 0;
}

  Bool
update_enabled(State* st)
{
  if (smem_act(st, 0)) {
    if (st->enabled == 0) {
      CMD_enable(st);
      return 1;
    }
  }
  else {
    if (st->enabled != 0) {
      CMD_disable(st);
      return 1;
    }
  }
  return 0;
}

// - Each variable is owned by a single process.
// - In each packet sent to another process, include the current
// values of all the variables it can read (that the sending process owns).

// States:
//   0. Disabled
//   1. Requesting

// Things I can do:
// - ACT: Perform an enabled action based on currently known values.
// - SEQ: Randomly assign/increment {src_seq} to a new value.
// - DISABLE: Assign {enabled} to zero. Also call SEQ.
// - ENABLE: Randomly assign {enabled} to some positive value. Also call SEQ.
// - SEND: Send info.


// Case: Both disabled.
// # If I receive a message which has the wrong sequence number for me,
// then SEND using my sequence number as {src_seq}
// # If I receieve a message which uses my correct sequence number,
// but I don't recognize the other's sequence number,
// then SEND.
// # If I don't receive a message after some timeout,
// then SEND.

// Case: I am disabled, neighbor is enabled to act.
// # If I get a message with a positive {enabled} value,
// then SEQ, SEND.

// Case: I am enabled to act.
// # ENABLE
// # If all reply using the new src_seq number and lower enabled values,
// then ACT, DISABLE, SEND.
// # If one of the replies has an {enabled} value greater than my own,
// then SEND. Don't do anything else.
// # If all reply using the new src_seq number and lower or
// equal enabled values (including equal values),
// then ENABLE, SEND.
// # If some message contains new values which disable all of my actions,
// then DISABLE, SEND.

  int
handle_recv (Packet* pkt, Channel* channel, State* st)
{
  Bool bcast = 0;
  Bool reply = 0;
  if (pkt->dst_seq != channel->seq) {
    pkt->dst_seq = pkt->src_seq;
    pkt->src_seq = channel->seq;
    pkt->enabled = st->enabled;
    pkt->state = st->x_me;
    send_Packet(pkt, &channel->host, st);
    return 1;
  }

  if (channel->adj_seq != pkt->src_seq) {
    channel->adj_seq = pkt->src_seq;
    reply = 1;
  }
  if (pkt->enabled != 0) {
    reply = 1;
  }

  if (channel == &st->channels[0]) {
    if (st->x_lo != pkt->state) {
      st->x_lo = pkt->state;
    }
  }
  else {
    if (st->x_hi != pkt->state) {
      st->x_hi = pkt->state;
    }
  }

  if (st->enabled != 0) {
    if (pkt->enabled < st->enabled) {
      channel->acknowledged = 1;
    }
  }

  if (update_enabled(st))
    bcast = 1;

  if (st->enabled != 0) {
    if (pkt->enabled == st->enabled) {
      CMD_enable(st);
      bcast = 1;
    }
  }

  if (st->enabled != 0 &&
      st->channels[0].acknowledged &&
      st->channels[1].acknowledged)
  {
    while (smem_act(st, 1)) {
      // Keep acting until disabled.
    }
    CMD_disable(st);
    bcast = 1;
  }

  pkt->enabled = st->enabled;
  pkt->state = st->x_me;
  if (bcast) {
    for (uint i = 0; i < 2; ++i) {
      pkt->src_seq = st->channels[i].seq;
      pkt->dst_seq = st->channels[i].adj_seq;
      send_Packet(pkt, &st->channels[i].host, st);
    }
    return 1;
  }
  else if (reply) {
    pkt->src_seq = channel->seq;
    pkt->dst_seq = channel->adj_seq;
    send_Packet(pkt, &channel->host, st);
    return 2;
  }

  return 0;
}

  void
handle_send_all (State* st)
{
  update_enabled(st);
  for (uint i = 0; i < 2; ++i) {
    Channel* channel = &st->channels[i];
    Packet pkt[1];
    pkt->src_seq = channel->seq;
    pkt->dst_seq = channel->adj_seq;
    pkt->enabled = st->enabled;
    pkt->state = st->x_me;
    send_Packet(pkt, &channel->host, st);
  }
}

static Bool terminating = 0;
static void set_term_flag()
{
  terminating = 1;
}

int main(int argc, char** argv)
{
  const uint BCastWaitLimit = 5;
  const uint TimeoutMS = TimeoutMS;
  State st[1];
  int argi = 1;
  uint PcIdx;
  uint NPcs;
  uint bcast_wait_count;
  if (argi + 2 != argc) {
    BailOut(1, "Need two arguments");
  }
  if (1 != sscanf(argv[argi++], "%u", &PcIdx))
    BailOut(1, "First argument must be an unsigned int.");

  if (1 != sscanf(argv[argi++], "%u", &NPcs) || NPcs == 0)
    BailOut(1, "Second argument must be a positive unsigned int.");

  /* remove("shared-resource"); */
  signal(SIGTERM, set_term_flag);
  signal(SIGINT, set_term_flag);

  init_State(st, PcIdx, NPcs);

  bcast_wait_count = BCastWaitLimit;
  while (!terminating)
  {
    Packet pkt[1];
    int stat;
    struct pollfd pfd[1];

    if (bcast_wait_count == BCastWaitLimit) {
      handle_send_all(st);
      bcast_wait_count = 0;
    }

    pfd->fd = st->fd;
    pfd->events = POLLIN;
    pfd->revents = 0;
    stat = poll(pfd, 1, 1000);

    if (stat == 0) {
      // We hit timeout, resend things.
      handle_send_all(st);
    }
    else if (stat == 1) {
      // Ok got message.
      Channel* channel = recv_Packet(pkt, st);
      if (channel) {
        if (2 == handle_recv(pkt, channel, st)) {
          bcast_wait_count = 0;
        }
      }
    }
    else {
      // Handle error
      failmsg("Some error in poll()");
    }
  }
  lose_State(st);
  return 0;
}

