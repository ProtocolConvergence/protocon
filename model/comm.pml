
//#define TestBandGt

#define MaxBand 3

#define ITE( a, b, c ) \
  (((a) && (b)) || (!(a) && (c)))

#define BandGt(a, b) \
  ITE((b) < (a), \
      ITE((b) <= MaxBand / 2, \
          (a) - (b) <= MaxBand / 2, \
          true), \
      (b) - (a) > MaxBand / 2)

#define IncBand(a)  ITE((a) == MaxBand, 0, (a) + 1)

#define WinByPcIdx  (_pid == 1)

#define band_t byte

#define Eql(name) (name##1 == name##0)


#if defined(TestBandGt)
init
{
  band_t a, b;
  select(a : 0..(MaxBand));
  select(b : 0..(MaxBand));

  if
  :: BandGt(a, b) ->
     assert(a != b);
     assert(!BandGt(b, a));
  :: BandGt(b, a) ->
     assert(a != b);
     assert(!BandGt(a, b));
  :: else ->
     assert(a == b);
     assert(!BandGt(a, b));
     assert(!BandGt(b, a));
  fi;
}

#else  /* ^^^ defined(TestBandGt) */

proctype fsm (chan xget, oput, byte pcidx)
{
  band_t oband0, oband1;
  band_t xband0, xband1;
  byte val0, val1;
  byte mode0, mode1;
  byte lval;
  byte lmode;

  select(oband0 : 0..(MaxBand));
  select(xband0 : 0..(MaxBand));
  select(val0 : 0..1);
  select(mode0 : 0..2);
  select(lval : 0..1);
  select(lmode : 0..2);

  printf ("%u %u %u %u %u %u %u\n", _pid,
          lval, lmode, oband0, xband0, val0, mode0);

  do
  :: true ->
     // Receive message.
     if
     :: atomic { nempty(xget) -> xget ? xband1, oband1, val1, mode1; }
     :: empty(xget) ->
        oband1 = oband0;
        xband1 = xband0;
        val1 = val0;
        mode1 = mode0;
     fi;

     if
     :: BandGt(oband0, oband1) ->
        if
        :: BandGt(xband1, xband0) ->
           // Neighbor corrupted.
           // Local data will be sent over with a higher band,
           // so the neighbor will figure it out.
           xband0 = xband1;
           val0 = val1;
           mode0 = mode1;
        :: else ->
           // Ignore old message.
           skip;
        fi;

     :: BandGt(oband1, oband0) ->
        // Neighbor corrupted my band.
        // Just use that copy plus one so a handshake occurs.
        oband0 = IncBand(oband1);
        if
        :: BandGt(xband1, xband0) ->
           xband0 = xband1;
        :: else -> skip;
        fi;
        val0 = val1;
        mode0 = mode1;

     :: Eql(oband) && BandGt(xband0, xband1) ->
        // Ignore old message.
        skip;

     :: Eql(oband) && BandGt(xband1, xband0) ->
        // New mode!
        xband0 = xband1;
        val0 = val1;
        mode0 = mode1;

     :: Eql(oband) && Eql(xband) && !Eql(val) ->
        oband0 = IncBand(oband0);
        val0 = val1;
        mode0 = 2;

     :: Eql(oband) && Eql(xband) && Eql(val) && Eql(mode) ->
        // Everything is up to date.
        skip;

     :: Eql(oband) && Eql(xband) && Eql(val) && !Eql(mode) ->
        if
        :: mode0 == 2 ->
           // Handshake completed.
           mode0 = mode1;
        :: else ->
           // Conflicting mode information.
           oband0 = IncBand(oband0);
           mode0 = 2;
        fi;
     fi;

     printf ("%u %u %u %u %u %u %u\n", _pid,
             lval, lmode, oband0, xband0, val0, mode0);
     // Stuff.

     // Send message.
     if
     :: atomic { nfull(oput) -> oput ! oband0, xband0, lval, lmode; }
     :: full(oput) -> skip;
     fi;
  od;
}

init
{
  chan io[2] = [1] of { band_t, band_t, byte, byte };
  run fsm(io[0], io[1], 0);
  run fsm(io[1], io[0], 1);
}

#define Legit \
  (fsm[0]:oband0 == fsm[1]:xband0 && \
   fsm[0]:xband0 == fsm[1]:oband0 && \
   fsm[0]:lval == fsm[1]:val0 && \
   fsm[1]:lval == fsm[0]:val0 && \
   fsm[0]:lmode == fsm[1]:mode0 && \
   fsm[1]:lmode == fsm[0]:mode0)

ltl {
  <> ([] Legit);
}
#endif  /* !defined(TestBandGt) */

