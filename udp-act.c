
//#define DoThreeColorRing
#define DoMatchingRing
//#define DoThreeBitTokenRing
//#define DoFoundThreeBitTokenRing

#ifdef DoThreeColorRing
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
#endif

#ifdef DoMatchingRing
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
#endif


#ifdef DoFoundThreeBitTokenRing
#define DoThreeBitTokenRing
#endif

#ifdef DoThreeBitTokenRing
  void
action_assign(uint32_t* x, uint PcIdx)
{
#ifdef DoFoundThreeBitTokenRing
  const Bool GoudaAndHaddixVersion = 0;
#else
  const Bool GoudaAndHaddixVersion = 1;
#endif
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

