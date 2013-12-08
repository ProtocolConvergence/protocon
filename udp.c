
#include "cx/def.h"
#include <stdint.h>
#include <stdio.h>
#include "udp-act.c"
#include <sys/types.h>
#include <netdb.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <signal.h>
#include <time.h>

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
  Bool adj_acknowledged;
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
  FILE* logf;
};

static const char SharedFilePfx[] = "udp-host.";
static const Bool ShowCommunication = 0;
//#define DebugLogging
static const uint TimeoutMS = 5000;


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

  Bool
next_urandom_Bool(State* st)
{
  uint8_t x;
  int stat;
  stat = read(st->urandom_fd, &x, sizeof(x));
  if (stat != sizeof(x))
    BailOut(-1, "next_urandom_Bool() -- read()");
  return x & 1;
}

  void
CMD_seq(Channel* channel, State* st)
{
  uint32_t* seq = &channel->seq;
  uint32_t x = 0;
  next_urandom(&x, st);
  x |= 0x0000FFFF;
  *seq += 1;
  *seq |= 0xFFFF0000;
  *seq &= x;
  channel->adj_acknowledged = 0;
}

  void
CMD_seq_all(State* st)
{
  for (uint i = 0; i < 2; ++i) {
    CMD_seq(&st->channels[i], st);
  }
}

  void
CMD_enable(State* st)
{
  next_urandom(&st->enabled, st);
  // Not allowed to 0.
  st->enabled |= (1 << 31);
  // Not allowed to be 0xFFFFFFFF.
  st->enabled ^= (1 << 30);
  CMD_seq_all(st);
}

  void
CMD_disable(State* st)
{
  st->enabled = 0;
  CMD_seq_all(st);
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
  CMD_seq(channel, st);
  channel->adj_seq = 0;
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
    Channel* channel = &st->channels[i];
    next_urandom(&channel->seq, st);
    next_urandom(&channel->adj_seq, st);
    channel->adj_acknowledged = next_urandom_Bool(st);
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
  if (st->logf)
    fclose(st->logf);
}

  void
oput_line(const char* line, const State* st)
{
  char timebuf[200];
  time_t t = time(0);
  struct tm *tmp;

  tmp = localtime(&t);
  if (tmp) {
    if (0 == strftime(timebuf, sizeof(timebuf), "%Y.%m.%d %H:%M:%S", tmp)) {
      timebuf[0] = '\0';
    }
  }
  else {
    timebuf[0] = '\0';
  }

  fprintf(stderr, "%s %2u %s\n", timebuf, st->PcIdx, line);
  if (st->logf)
    fprintf(st->logf, "%s %2u %s\n", timebuf, st->PcIdx, line);
}

  int
send_Packet (const Packet* packet, const struct sockaddr_in* host, const State* st)
{
  Packet pkt[1];
  int stat;
  *pkt = *packet;
  if (ShowCommunication) {
    char buf[512];
    sprintf(buf, "-> %2u  (%u %u %u)  src_seq:%08x  dst_seq:%08x  enabled:%08x  state:%u",
            ((&st->channels[0].host == host)
             ? st->channels[0].adj_PcIdx
             : st->channels[1].adj_PcIdx),
            st->x_lo, st->x_me, st->x_hi,
            pkt->src_seq,
            pkt->dst_seq,
            pkt->enabled,
            pkt->state);
    oput_line(buf, st);
  }
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
      if (ShowCommunication) {
        char buf[512];
        sprintf(buf, "<- %2u  (%u %u %u)  src_seq:%08x  dst_seq:%08x  enabled:%08x  state:%u",
                channel->adj_PcIdx,
                st->x_lo, st->x_me, st->x_hi,
                pkt->src_seq,
                pkt->dst_seq,
                pkt->enabled,
                pkt->state);
        oput_line(buf, st);
      }
      return channel;
    }
  }

  BailOut(0, "who sent the message?");
}

  Bool
CMD_act(State* st, Bool modify)
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

      {
        uint32_t x = 0;
        next_urandom(&x, st);
        // This helps the scheduler find livelocks.
        //usleep(10000);
        usleep(1000 * (x % 256));
      }

      if (true) {
        char buf[1024];
        sprintf(buf, " ACT:  x[%u]==%u && x[%u]==%u && x[%u]==%u --> x[%u]:=%u;",
                st->channels[0].adj_PcIdx, x[i-1],
                st->PcIdx, st->x_me,
                st->channels[1].adj_PcIdx, x[i+1],
                st->PcIdx, x[i]);
        oput_line(buf, st);
      }
      st->x_me = x[i];
    }
    return 1;
  }
  return 0;
}

  void
CMD_send(Channel* channel, State* st)
{
  Packet pkt[1];
  pkt->src_seq = channel->seq;
  pkt->dst_seq = channel->adj_seq;
  pkt->enabled = st->enabled;
  pkt->state = st->x_me;
  send_Packet(pkt, &channel->host, st);
}

  void
CMD_send_all(State* st)
{
  for (uint i = 0; i < 2; ++i) {
    Channel* channel = &st->channels[i];
    CMD_send(channel, st);
  }
}

  Bool
update_enabled(State* st)
{
  // Sanitize this value.
  if (~st->enabled == 0)
    st->enabled = 0;

  if (CMD_act(st, 0)) {
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

/**
 * - Each variable is owned by a single process.
 * - In each packet sent to another process, include the current
 * values of all the variables it can read (that the sending process owns).
 *
 * States:
 *   0. Disabled
 *   1. Requesting
 *
 * Things I can do:
 * - ACT: Perform an enabled action based on currently known values.
 *   \sa CMD_act()
 * - SEQ: Randomly assign/increment {src_seq} to a new value.
 *   \sa CMD_seq()
 * - SEQ_ALL: Call SEQ for all channels.
 *   \sa CMD_seq_all()
 * - DISABLE: Assign {enabled} to zero. Also call SEQ.
 *   \sa CMD_disable()
 * - ENABLE: Randomly assign {enabled} to some positive value. Also call SEQ.
 *   \sa CMD_enable()
 * - SEND: Send info.
 *   \sa CMD_send()
 * - SEND_ALL: Send info to all.
 *   \sa CMD_send_all()
 *
 *
 * Case: Both disabled.
 * # If I receive a message which has the wrong sequence number for me,
 * then SEND using my sequence number as {src_seq}
 * # If I receieve a message which uses my correct sequence number,
 * but I don't recognize the other's sequence number,
 * then SEND.
 * # If I don't receive a message after some timeout,
 * then SEND.
 *
 * Case: I am disabled, neighbor is enabled to act.
 * # If I get a message with a positive {enabled} value,
 * then SEQ, SEND.
 *
 * Case: I am enabled to act.
 * # ENABLE
 * # If all reply using the new src_seq number and lower enabled values,
 * then ACT, DISABLE, SEND.
 * # If one of the replies has an {enabled} value greater than my own,
 * then SEND. Don't do anything else.
 * # If all reply using the new src_seq number and lower or
 * equal enabled values (including equal values),
 * then ENABLE, SEND.
 * # If some message contains new values which disable all of my actions,
 * then DISABLE, SEND.
 */
  int
handle_recv (Packet* pkt, Channel* channel, State* st)
{
  Bool bcast = 0;
  Bool reply = 0;
  Bool adj_acted = 0;

  // If the packet doesn't know this process's sequence number,
  // then reply with the current data.
  if (pkt->dst_seq != channel->seq) {
    pkt->dst_seq = pkt->src_seq;
    pkt->src_seq = channel->seq;
    if (false && channel->adj_acknowledged) {
      // 50% chance of not replying.
      if (0 == next_urandom_Bool(st)) {
        return 0;
      }
    }
#if 1
    // This is faster when no fairness is assumed.
    if (st->enabled != 0 && st->enabled < pkt->enabled) {
      pkt->enabled = 0xFFFFFFFF;
    }
    else {
      pkt->enabled = st->enabled;
    }
#else
    pkt->enabled = 0xFFFFFFFF;
#endif
    pkt->state = st->x_me;
    send_Packet(pkt, &channel->host, st);
    return 1;
  }

  // Update the current values of the adjacent process's states.
  if (channel == &st->channels[0]) {
    if (st->x_lo != pkt->state) {
      st->x_lo = pkt->state;
      adj_acted = 1;
    }
  }
  else {
    if (st->x_hi != pkt->state) {
      st->x_hi = pkt->state;
      adj_acted = 1;
    }
  }

  if (st->enabled != 0) {
    // This process is enabled and waiting to act.
    // It has updated its sequence number already
    // and has sent its intent to act to the adjacent processes.
    if (pkt->enabled < st->enabled) {
      // The adjacent process is disabled or has a lower priority than this process.
      // It knows our current sequence number,
      // so count that as an acknowledgment that this process can act.
      channel->adj_acknowledged = 1;
    }
  }

  // If this process just became enabled or disabled,
  // then update the sequence number and prepare to broadcast
  // to all adjacent processes.
  if (update_enabled(st)) {
    bcast = 1;
  }
  else if (adj_acted && st->enabled == 0) {
    CMD_seq(channel, st);
    //reply = 1;
  }

  if (channel->adj_seq != pkt->src_seq) {
    // The adjacent process updated its sequence number.
    channel->adj_seq = pkt->src_seq;
    // If it is enabled (just became enabled),
    // then this process should reply.
    if (pkt->enabled != 0) {
      reply = 1;
      if (~pkt->enabled != 0 && st->enabled == 0 && pkt->dst_seq == channel->seq) {
        CMD_seq(channel, st);
      }
    }
  }

  if (st->enabled != 0) {
    // This process is enabled.
    if (pkt->enabled == st->enabled) {
      // The adjacent process has the same priority to act!
      // Update our priority and sequence number.
      // All adjacent processes must acknowledge before we can act.
      CMD_enable(st);
      bcast = 1;
    }
    else if (pkt->enabled > st->enabled) {
      if (~pkt->enabled != 0) {
        CMD_seq(channel, st);
      }
    }

    if (channel->adj_acknowledged) {
      // No need to reply when the adjacent process already
      // acknowledged that this process can act.
      reply = 0;
    }
  }
  else if (pkt->dst_seq == channel->seq) {
    channel->adj_acknowledged = 1;
  }

  if (st->enabled != 0 &&
      st->channels[0].adj_acknowledged &&
      st->channels[1].adj_acknowledged)
  {
    // This process is enabled and all adjacent processes
    // have acknowledged that it can act!
    while (CMD_act(st, 1)) {
      // Keep acting until disabled.
    }
    CMD_disable(st);
    bcast = 1;
  }

  // Any outgoing message contains our current enabled status and state.
  if (bcast) {
    // We are broadcasting to all adjacent processes.
    CMD_send_all(st);
    // Return that a broadcast occurred.
    return 2;
  }
  else if (reply) {
    // Just reply to the sending process.
    CMD_send(channel, st);
    // Return that a reply occurred.
    return 1;
  }

  return 0;
}

  void
handle_send_all (State* st)
{
  update_enabled(st);
  CMD_send_all(st);
}

static Bool terminating = 0;
static Bool randomize_state_flag = 0;
static void set_term_flag()
{
  terminating = 1;
}

static void set_randomize_state_flag()
{
  randomize_state_flag = 1;
}


static int
init_timeout(timer_t* timeout_id)
{
  struct sigevent timeout_sigevent[1];
  int stat = 0;
  memset(timeout_sigevent, 0, sizeof(*timeout_sigevent));
  timeout_sigevent->sigev_notify = SIGEV_NONE;
  stat = timer_create(CLOCK_REALTIME, timeout_sigevent, timeout_id);
  if (stat != 0)
    BailOut(stat, "timer_create()");
  return 0;
}

static int
reset_timeout(timer_t timeout_id) {
  struct itimerspec timeout_spec[1];
  int stat = 0;
  memset(timeout_spec, 0, sizeof(*timeout_spec));
  timeout_spec->it_value.tv_sec = TimeoutMS / 1000;
  timeout_spec->it_value.tv_nsec = 1000000 * (TimeoutMS % 1000);
  stat = timer_settime(timeout_id, 0, timeout_spec, 0);
  if (stat != 0)
    BailOut(stat, "timer_settime()");
  return 0;
}

int main(int argc, char** argv)
{
  State st[1];
  int argi = 1;
  uint PcIdx;
  uint NPcs;
  timer_t timeout_id;
  uint timeout_ms = 0;
  if (argi + 2 > argc) {
    BailOut(1, "Need two or three arguments");
  }
  if (1 != sscanf(argv[argi++], "%u", &PcIdx))
    BailOut(1, "First argument must be an unsigned int.");

  if (1 != sscanf(argv[argi++], "%u", &NPcs) || NPcs == 0)
    BailOut(1, "Second argument must be a positive unsigned int.");

  /* remove("shared-resource"); */
  signal(SIGTERM, set_term_flag);
  signal(SIGINT, set_term_flag);
  signal(SIGUSR1, set_randomize_state_flag);

  init_timeout(&timeout_id);

  init_State(st, PcIdx, NPcs);
  if (argv[argi]) {
    st->logf = fopen(argv[argi++], "wb");
  }

  while (!terminating)
  {
    Packet pkt[1];
    int stat;
    struct pollfd pfd[1];

    pfd->fd = st->fd;
    pfd->events = POLLIN;
    pfd->revents = 0;
    stat = poll(pfd, 1, timeout_ms);

    if (randomize_state_flag) {
      randomize_State(st);
      randomize_state_flag = 0;
    }

    if (stat == 0) {
      // We hit timeout, resend things.
      handle_send_all(st);
      reset_timeout(timeout_id);
    }
    else if (stat == 1) {
      // Ok got message.
      Channel* channel = recv_Packet(pkt, st);
      if (channel) {
        if (2 == handle_recv(pkt, channel, st)) {
          reset_timeout(timeout_id);
        }
      }
    }
    else {
      // Handle error
      failmsg("Some error in poll()");
    }

    {
      struct itimerspec timeout_info[1];
      if (0 == timer_gettime(timeout_id, timeout_info)) {
        timeout_ms = timeout_info->it_value.tv_sec * 1000;
        timeout_ms += timeout_info->it_value.tv_nsec / 1000000;
      }
    }
  }
  timer_delete(timeout_id);
  lose_State(st);
  return 0;
}

