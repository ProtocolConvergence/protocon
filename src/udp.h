
#include "cx/def.h"
#include <stdint.h>
#include <stdio.h>
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

// Can leave this undefined.
//#define FixedHostname "10.0.0.1"

static const Bool ShowTimestamps = 1;
static const Bool ShowCommunication = 0;
static const uint TimeoutMS = 10000;
static const uint QuickTimeoutMS = 200;
//static const uint QuickTimeoutMS = 20;
#define NQuickTimeouts (TimeoutMS / QuickTimeoutMS)
static const double NetworkReliability = 1;
//static const double NetworkReliability = 0.5;
//static const double NetworkReliability = 0.1;
static const uint32_t ActionLagMS = 256;
//static const uint32_t ActionLagMS = 0;
static const char SharedFilePfx[] = "udp-host.";

typedef int fd_t;

typedef struct PcIden PcIden;
struct PcIden
{
  uint idx;
  uint npcs;
};

static void
oput_line(const char* line);

static uint
process_of_channel(PcIden pc, uint channel_idx);
static uint
variable_of_channel(PcIden pc, uint channel_idx, uint i, Bool writing);
static uint
domsz_of_variable(PcIden pc, uint vbl_idx);
static void
action_assign(PcIden pc, uint8_t* values);
static void
action_pre_assign(PcIden pc, const uint8_t* x);
#define Max_NChannels 2
#define Max_NVariables 4
#include "udp-act.h"

