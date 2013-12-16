
//#define DoThreeColorRing
#define DoMatchingRing
//#define DoThreeBitTokenRing
//#define DoFoundThreeBitTokenRing
//#define DoDijkstraFourState

/****************************************************************************/
#ifdef DoThreeColorRing
  uint
process_of_channel(PcIden pc, uint channel_idx)
{
  if (channel_idx == 0)  return (pc.idx + pc.npcs - 1) % pc.npcs;
  if (channel_idx == 1)  return (pc.idx + 1) % pc.npcs;
  return pc.idx;
}

  uint
variable_of_channel(PcIden pc, uint channel_idx, uint i, Bool writing)
{
  (void) pc;
  if (writing) {
    if (channel_idx == 0 && i == 0)  return 1;
    if (channel_idx == 1 && i == 0)  return 1;
    return Max_NVariables;
  }
  if (channel_idx == 0 && i == 0)  return 0;
  if (channel_idx == 1 && i == 0)  return 2;
  return Max_NVariables;
}

  uint
domsz_of_variable(PcIden pc, uint vbl_idx)
{
  (void) pc;
  if (vbl_idx < 3)  return 3;
  return 0;
}

  void
action_assign(PcIden pc, uint8_t* c)
{
  // 3-coloring
  const uint i = 1;
  (void) pc ;
  if (c[i] >= 3)  c[i] %= 3;
  while (c[i-1] == c[i] || c[i] == c[i+1]) {
    c[i] += 1;
    c[i] %= 3;
  }
}
  void
action_pre_assign(PcIden pc, const uint8_t* c)
{
  uint8_t c_img[Max_NVariables];
  char buf[1024];
  memcpy(c_img, c, sizeof(c_img));
  action_assign(pc, c_img);
  sprintf(buf, " ACT:  c[%u]==%u && c[%u]==%u && c[%u]==%u --> c[%u]:=%u;",
          process_of_channel(pc, 0), c[0],
          pc.idx, c[1],
          process_of_channel(pc, 1), c[2],
          pc.idx, c_img[1]);
  oput_line(buf);
}
#endif

/****************************************************************************/
#ifdef DoMatchingRing
  uint
process_of_channel(PcIden pc, uint channel_idx)
{
  if (channel_idx == 0)  return (pc.idx + pc.npcs - 1) % pc.npcs;
  if (channel_idx == 1)  return (pc.idx + 1) % pc.npcs;
  return pc.idx;
}

  uint
variable_of_channel(PcIden pc, uint channel_idx, uint i, Bool writing)
{
  (void) pc;
  if (writing) {
    if (channel_idx == 0 && i == 0)  return 1;
    if (channel_idx == 1 && i == 0)  return 1;
    return Max_NVariables;
  }
  if (channel_idx == 0 && i == 0)  return 0;
  if (channel_idx == 1 && i == 0)  return 2;
  return Max_NVariables;
}

  uint
domsz_of_variable(PcIden pc, uint vbl_idx)
{
  (void) pc;
  if (vbl_idx < 3)  return 3;
  return 0;
}

  void
action_assign(PcIden pc, uint8_t* x)
{
  // Matching
  const uint i = 1;
  (void) pc;
  if (x[i-1]==1 && x[i]!=0 && x[i+1]==2)  x[i]=0;
  if (x[i-1]!=1 && x[i]==0 && x[i+1]!=2)  x[i]=2;
  if (x[i-1]!=1 && x[i]!=1 && x[i+1]==2)  x[i]=1;
  if (x[i-1]==1 && x[i]!=2 && x[i+1]!=2)  x[i]=2;
}
  void
action_pre_assign(PcIden pc, const uint8_t* x)
{
  uint8_t x_img[Max_NVariables];
  char buf[1024];
  memcpy(x_img, x, sizeof(x_img));
  action_assign(pc, x_img);
  sprintf(buf, " ACT:  x[%u]==%u && x[%u]==%u && x[%u]==%u --> x[%u]:=%u;",
          process_of_channel(pc, 0), x[0],
          pc.idx, x[1],
          process_of_channel(pc, 1), x[2],
          pc.idx, x_img[1]);
  oput_line(buf);
}
#endif


/****************************************************************************/
#ifdef DoFoundThreeBitTokenRing
#define DoThreeBitTokenRing
#endif

#ifdef DoThreeBitTokenRing
#undef Max_NVariables
#define Max_NVariables 8
  uint
process_of_channel(PcIden pc, uint channel_idx)
{
  if (channel_idx == 0)  return (pc.idx + pc.npcs - 1) % pc.npcs;
  if (channel_idx == 1)  return (pc.idx + 1) % pc.npcs;
  return pc.idx;
}

  uint
variable_of_channel(PcIden pc, uint channel_idx, uint i, Bool writing)
{
  (void) pc;
  if (writing) {
    if (channel_idx == 1 && i == 0)  return 1;
    if (channel_idx == 1 && i == 1)  return 3;
    return Max_NVariables;
  }
  if (channel_idx == 0 && i == 0)  return 0;
  if (channel_idx == 0 && i == 1)  return 2;
  return Max_NVariables;
}

  uint
domsz_of_variable(PcIden pc, uint vbl_idx)
{
  (void) pc;
  if (vbl_idx < 5)  return 2;
  return 0;
}

  void
action_assign(PcIden pc, uint8_t* x)
{
#ifdef DoFoundThreeBitTokenRing
  const Bool GoudaAndHaddixVersion = 0;
#else
  const Bool GoudaAndHaddixVersion = 1;
#endif
  const uint i = 1;
  uint8_t* e = &x[0];
  uint8_t* t = &x[2];
  uint8_t* ready = &x[3];

  if (GoudaAndHaddixVersion) {
    if (pc.idx == 0) {
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
    if (pc.idx == 0) {
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
}
  void
action_pre_assign(PcIden pc, const uint8_t* x)
{
  uint8_t x_img[Max_NVariables];
  char buf[1024];
  memcpy(x_img, x, sizeof(x_img));
  action_assign(pc, x_img);
  if ((pc.idx == 0 && x[2] == x[3])
      ||
      (pc.idx != 0 && x[2] != x[3]))
  {
    if (false) {
      FILE* f = fopen("shared-resource", "ab");
      fprintf(f, "%u\n", pc.idx);
      fclose(f);
    }
    fprintf(stderr, "%u WRITING TO SHARED RESOURCE\n", pc.idx);
  }
  if (false) {
  sprintf(buf, " ACT:  e[%u]==%u && e[%u]==%u && t[%u]==%u && t[%u]==%u && ready[%u]==%u --> t[%u]:=%u; e[%u]:=%u; ready[%u]:=%u;",
          process_of_channel(pc, 0), x[0],
          pc.idx, x[1],
          process_of_channel(pc, 0), x[2],
          pc.idx, x[3],
          pc.idx, x[4],
          pc.idx, x_img[1],
          pc.idx, x_img[3],
          pc.idx, x_img[4]);
  oput_line(buf);
  }
}
#endif

#ifdef DoDijkstraFourState
#undef Max_NVariables
#define Max_NVariables 8
  uint
process_of_channel(PcIden pc, uint channel_idx)
{
  if (pc.idx == 0 && channel_idx == 0)  return 1;
  if (pc.idx == pc.npcs-1 && channel_idx == 0)  return pc.idx-1;
  if (pc.idx > 0 && pc.idx < pc.npcs-1) {
    if (channel_idx == 0)  return pc.idx-1;
    if (channel_idx == 1)  return pc.idx+1;
  }
  return pc.idx;
}

  uint
variable_of_channel(PcIden pc, uint channel_idx, uint i, Bool writing)
{
  if (writing) {
    if (pc.idx == 0 && channel_idx == 0 && i == 0)  return 2; // z[i]
    if (pc.idx == pc.npcs-1 && channel_idx == 0 && i == 0)  return 0; // up[i]
    if (pc.idx == pc.npcs-1 && channel_idx == 0 && i == 1)  return 2; // z[i]
    if (pc.idx > 0 && pc.idx < pc.npcs-1 && channel_idx == 0 && i == 0)  return 0; // up[i]
    if (pc.idx > 0 && pc.idx < pc.npcs-1 && channel_idx == 0 && i == 1)  return 3; // z[i]
    if (pc.idx > 0 && pc.idx < pc.npcs-1 && channel_idx == 1 && i == 0)  return 3; // z[i]

    return Max_NVariables;
  }
  if (pc.idx == 0 && channel_idx == 0 && i == 0)  return 1; // up[i+1]
  if (pc.idx == 0 && channel_idx == 0 && i == 1)  return 3; // z[i+1]
  if (pc.idx == pc.npcs-1 && channel_idx == 0 && i == 0)  return 1; // z[i-1]
  if (pc.idx > 0 && pc.idx < pc.npcs-1 && channel_idx == 0 && i == 0)  return 2; // z[i-1]
  if (pc.idx > 0 && pc.idx < pc.npcs-1 && channel_idx == 1 && i == 0)  return 1; // up[i+1]
  if (pc.idx > 0 && pc.idx < pc.npcs-1 && channel_idx == 1 && i == 1)  return 4; // z[i+1]
  return Max_NVariables;
}

  uint
domsz_of_variable(PcIden pc, uint vbl_idx)
{
  if (pc.idx == 0 && vbl_idx < 4)  return 2;
  if (pc.idx == pc.npcs-1 && vbl_idx < 3)  return 2;
  if (pc.idx > 0 && pc.idx < pc.npcs-1 && vbl_idx < 5)  return 2;
  return 0;
}

  void
action_assign(PcIden pc, uint8_t* x)
{
  const uint i = 1;
  uint8_t* up;
  uint8_t* z;

  if (pc.idx == 0) {
    up = &x[-1];
    z = &x[1];
    if ((up[i] == 0) || (up[i+1] == 0 && z[i] == z[i+1])) {
      up[i] = 1;
      z[i] = 1 - z[i+1];
    }
  }
  else if (pc.idx == pc.npcs-1) {
    up = &x[-1];
    z = &x[1];
    if ((up[i] == 1) || (z[i-1] != z[i])) {
      up[i] = 0;
      z[i] = z[i-1];
    }
  }
  else {
    up = &x[-1];
    z = &x[2];
    if (z[i-1]!=z[i] && !(up[i+1]==0 && z[i-1]==z[i+1])) {
      up[i] = 1;
      z[i] = z[i-1];
    }
    if (z[i-1]==z[i] && up[i]==1 && (up[i+1]==0 && z[i-1]==z[i+1])) {
      up[i] = 0;
    }
  }
}
  void
action_pre_assign(PcIden pc, const uint8_t* x)
{
  uint8_t x_img[Max_NVariables];
  char buf[1024];
  memcpy(x_img, x, sizeof(x_img));
  action_assign(pc, x_img);
  if (pc.idx == 0) {
    sprintf(buf, " ACT:  up[0]==%u && up[1]==%u && z[0]==%u && z[1]==%u --> up[0]:=%u; z[0]:=%u;",
            x[0], x[1], x[2], x[3], x_img[0], x_img[2]);
  }
  else if (pc.idx == pc.npcs-1) {
    sprintf(buf, " ACT:  up[%u]==%u && z[%u]==%u && z[%u]==%u --> up[%u]:=%u; z[%u]:=%u;",
            pc.idx, x[0], pc.idx-1, x[1], pc.idx, x[2],
            pc.idx, x_img[0], pc.idx, x_img[2]);
  }
  else {
    sprintf(buf, " ACT:  up[%u]==%u && up[%u]==%u && z[%u]==%u && z[%u]==%u && z[%u]==%u --> up[%u]:=%u; z[%u]:=%u;",
            pc.idx, x[0], pc.idx+1, x[1], pc.idx-1, x[2], pc.idx, x[3], pc.idx+1, x[4],
            pc.idx, x_img[0], pc.idx, x_img[2]);
  }
  oput_line(buf);
}
#endif

