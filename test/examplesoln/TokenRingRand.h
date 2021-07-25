
#define Max_NChannels 2
#define Max_NVariables 3
#define NProcesses 10
uint process_of_channel(PcIden pc, uint channel_idx)
{
#define T(ret)  if (0==channel_idx)  return ret; channel_idx -= 1
  switch (pc.idx) {
  case 0: T( 9 ); T( 1 ); break;
  case 1: T( 0 ); T( 2 ); break;
  case 2: T( 1 ); T( 3 ); break;
  case 3: T( 2 ); T( 4 ); break;
  case 4: T( 3 ); T( 5 ); break;
  case 5: T( 4 ); T( 6 ); break;
  case 6: T( 5 ); T( 7 ); break;
  case 7: T( 6 ); T( 8 ); break;
  case 8: T( 7 ); T( 9 ); break;
  case 9: T( 8 ); T( 0 ); break;
  default: break;
  }
  return pc.idx;
#undef T
}
uint variable_of_channel(PcIden pc, uint channel_idx, uint i, Bool writing)
{
  if (pc.idx < 10) {
    if (writing) {
      if (channel_idx==1 && i==0)  return 1;
    }
    else {
      if (channel_idx==0 && i==0)  return 0;
    }
  }
  return Max_NVariables;
}
uint domsz_of_variable(PcIden pc, uint vbl_idx)
{
  if (0) {}
  else if (pc.idx < 1) {
    if (vbl_idx==0)  return 3;
    if (vbl_idx==1)  return 3;
    if (vbl_idx==2)  return 2;
  }
  else if (pc.idx < 10) {
    if (vbl_idx==0)  return 3;
    if (vbl_idx==1)  return 3;
  }
  return 0;
}
void assume_assign(PcIden pc, uint8_t* x)
{
  if (0) {
  }
  else if (pc.idx < 1) {
  }
  else if (pc.idx < 10) {
  }
}
void action_assign(PcIden pc, uint8_t* x)
{
  uint8_t tmp_x[Max_NVariables];
  memcpy(tmp_x, x, sizeof(tmp_x));
  if (0) {}
  else if (pc.idx < 1) {
    x[2] = RandomMod(2);
    /* */if (x[0]==0 && x[1]==0 && x[2]==0) switch (RandomMod(2)) {
      case 0: x[1]=1; break;
      case 1: x[1]=2; break;
    }
    else if (x[0]==0 && x[1]==0 && x[2]==1) switch (RandomMod(2)) {
      case 0: x[1]=1; break;
      case 1: x[1]=2; break;
    }
    else if (x[0]==1 && x[1]==1 && x[2]==0) switch (RandomMod(2)) {
      case 0: x[1]=0; break;
      case 1: x[1]=2; break;
    }
    else if (x[0]==1 && x[1]==1 && x[2]==1) switch (RandomMod(2)) {
      case 0: x[1]=0; break;
      case 1: x[1]=2; break;
    }
    else if (x[0]==2 && x[1]==2 && x[2]==0) switch (RandomMod(2)) {
      case 0: x[1]=0; break;
      case 1: x[1]=1; break;
    }
    else if (x[0]==2 && x[1]==2 && x[2]==1) switch (RandomMod(2)) {
      case 0: x[1]=0; break;
      case 1: x[1]=1; break;
    }
    else { memcpy(x, tmp_x, sizeof(tmp_x)); }
  }
  else if (pc.idx < 10) {
    /* */if (x[0]==0 && x[1]==1) { x[1]=0; }
    else if (x[0]==0 && x[1]==2) { x[1]=0; }
    else if (x[0]==1 && x[1]==0) { x[1]=1; }
    else if (x[0]==1 && x[1]==2) { x[1]=1; }
    else if (x[0]==2 && x[1]==0) { x[1]=2; }
    else if (x[0]==2 && x[1]==1) { x[1]=2; }
    else { memcpy(x, tmp_x, sizeof(tmp_x)); }
  }
}
void action_assign_hook(PcIden pc, const uint8_t* x_pre, const uint8_t* x_img)
{
  oput_line("ACTING!");
}
