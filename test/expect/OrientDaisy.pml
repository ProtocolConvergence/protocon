
#define N (5)
#define Chain (1)
bit initialized;
bit b[5];
bit w[10];

init {
  atomic{//Begin atomic initialization.
  if :: b[0] = 0; :: b[0] = 1; fi;
  if :: b[1] = 0; :: b[1] = 1; fi;
  if :: b[2] = 0; :: b[2] = 1; fi;
  if :: b[3] = 0; :: b[3] = 1; fi;
  if :: b[4] = 0; :: b[4] = 1; fi;
  if :: w[0] = 0; :: w[0] = 1; fi;
  if :: w[1] = 0; :: w[1] = 1; fi;
  if :: w[2] = 0; :: w[2] = 1; fi;
  if :: w[3] = 0; :: w[3] = 1; fi;
  if :: w[4] = 0; :: w[4] = 1; fi;
  if :: w[5] = 0; :: w[5] = 1; fi;
  if :: w[6] = 0; :: w[6] = 1; fi;
  if :: w[7] = 0; :: w[7] = 1; fi;
  if :: w[8] = 0; :: w[8] = 1; fi;
  if :: w[9] = 0; :: w[9] = 1; fi;
  initialized = 1;
  }//End atomic initialization.
}

// Just in case you use the if/then/else construct from {protocon}.
#define if
#define then ->
#define else :

active [2] proctype End()
{
#define tid (_pid - 1)
  int i = tid*(N-1);
#undef tid
  (initialized==1);
#define ij (if (i==0) then (2*i+1) else (2*i))
#define j (if (i==0) then (i+1) else (i-1))
#define ji (if (i==0) then (2*j) else (2*j+1))
end_End:
  do
  :: atomic { b[i]==0 && w[ij]==0 && b[j]==0 && w[ji]==0 -> b[i]=1; w[ij]=0; }
  :: atomic { b[i]==0 && w[ij]==0 && b[j]==0 && w[ji]==1 -> b[i]=1; w[ij]=1; }
  :: atomic { b[i]==0 && w[ij]==0 && b[j]==1 && w[ji]==0 -> b[i]=1; w[ij]=1; }
  :: atomic { b[i]==0 && w[ij]==0 && b[j]==1 && w[ji]==1 -> b[i]=1; w[ij]=0; }
  :: atomic { b[i]==0 && w[ij]==1 && b[j]==0 && w[ji]==0 -> b[i]=1; w[ij]=0; }
  :: atomic { b[i]==0 && w[ij]==1 && b[j]==0 && w[ji]==1 -> b[i]=1; w[ij]=1; }
  :: atomic { b[i]==0 && w[ij]==1 && b[j]==1 && w[ji]==0 -> b[i]=1; w[ij]=1; }
  :: atomic { b[i]==0 && w[ij]==1 && b[j]==1 && w[ji]==1 -> b[i]=1; w[ij]=0; }
  :: atomic { b[i]==1 && w[ij]==0 && b[j]==0 && w[ji]==1 -> b[i]=1; w[ij]=1; }
  :: atomic { b[i]==1 && w[ij]==0 && b[j]==1 && w[ji]==0 -> b[i]=1; w[ij]=1; }
  :: atomic { b[i]==1 && w[ij]==1 && b[j]==0 && w[ji]==0 -> b[i]=1; w[ij]=0; }
  :: atomic { b[i]==1 && w[ij]==1 && b[j]==1 && w[ji]==1 -> b[i]=1; w[ij]=0; }
  od;
#undef ij
#undef j
#undef ji
}

active [3] proctype P()
{
#define tid (_pid - 3)
  int i = tid+Chain;
#undef tid
  (initialized==1);
#define ij (2*i)
#define j (i-1)
#define ji (2*j+1)
#define ik (2*i+1)
#define k (i+1)
#define ki (2*k)
end_P:
  do
  :: atomic { b[i]==0 && w[ij]==0 && w[ik]==1 && b[j]==0 && b[k]==0 && w[ji]==0 && w[ki]==1 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==0 && w[ij]==1 && w[ik]==0 && b[j]==0 && b[k]==0 && w[ji]==1 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==0 && w[ij]==0 && w[ik]==1 && b[j]==0 && b[k]==0 && w[ji]==1 && w[ki]==1 -> b[i]=1; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==0 && w[ij]==1 && w[ik]==0 && b[j]==0 && b[k]==0 && w[ji]==1 && w[ki]==1 -> b[i]=1; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==0 && w[ij]==0 && w[ik]==1 && b[j]==0 && b[k]==1 && w[ji]==0 && w[ki]==1 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==0 && w[ij]==1 && w[ik]==0 && b[j]==1 && b[k]==0 && w[ji]==1 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==0 && w[ij]==0 && w[ik]==1 && b[j]==0 && b[k]==1 && w[ji]==1 && w[ki]==1 -> b[i]=1; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==0 && w[ij]==1 && w[ik]==0 && b[j]==1 && b[k]==0 && w[ji]==1 && w[ki]==1 -> b[i]=1; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==0 && w[ij]==0 && w[ik]==1 && b[j]==1 && b[k]==0 && w[ji]==0 && w[ki]==1 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==0 && w[ij]==1 && w[ik]==0 && b[j]==0 && b[k]==1 && w[ji]==1 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==0 && w[ij]==0 && w[ik]==1 && b[j]==1 && b[k]==0 && w[ji]==1 && w[ki]==1 -> b[i]=1; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==0 && w[ij]==1 && w[ik]==0 && b[j]==0 && b[k]==1 && w[ji]==1 && w[ki]==1 -> b[i]=1; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==0 && w[ij]==0 && w[ik]==1 && b[j]==1 && b[k]==1 && w[ji]==0 && w[ki]==1 -> b[i]=1; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==0 && w[ij]==1 && w[ik]==0 && b[j]==1 && b[k]==1 && w[ji]==1 && w[ki]==0 -> b[i]=1; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==0 && w[ij]==0 && w[ik]==1 && b[j]==1 && b[k]==1 && w[ji]==1 && w[ki]==0 -> b[i]=1; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==0 && w[ij]==1 && w[ik]==0 && b[j]==1 && b[k]==1 && w[ji]==0 && w[ki]==1 -> b[i]=1; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==0 && b[k]==0 && w[ji]==0 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==0 && b[k]==0 && w[ji]==0 && w[ki]==0 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==0 && b[k]==0 && w[ji]==0 && w[ki]==1 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==0 && b[k]==0 && w[ji]==1 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==0 && b[k]==0 && w[ji]==1 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==0 && b[k]==0 && w[ji]==0 && w[ki]==1 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==0 && b[k]==1 && w[ji]==0 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==1 && b[k]==0 && w[ji]==0 && w[ki]==0 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==0 && b[k]==1 && w[ji]==0 && w[ki]==1 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==1 && b[k]==0 && w[ji]==1 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==0 && b[k]==1 && w[ji]==1 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==1 && b[k]==0 && w[ji]==0 && w[ki]==1 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==0 && b[k]==1 && w[ji]==1 && w[ki]==1 -> b[i]=1; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==1 && b[k]==0 && w[ji]==1 && w[ki]==1 -> b[i]=1; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==1 && b[k]==0 && w[ji]==0 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==0 && b[k]==1 && w[ji]==0 && w[ki]==0 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==1 && b[k]==0 && w[ji]==0 && w[ki]==1 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==0 && b[k]==1 && w[ji]==1 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==1 && b[k]==0 && w[ji]==1 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==0 && b[k]==1 && w[ji]==0 && w[ki]==1 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==1 && b[k]==1 && w[ji]==0 && w[ki]==0 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==1 && b[k]==1 && w[ji]==0 && w[ki]==0 -> b[i]=0; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==1 && b[k]==1 && w[ji]==0 && w[ki]==1 -> b[i]=1; w[ij]=1; w[ik]=0; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==1 && b[k]==1 && w[ji]==1 && w[ki]==0 -> b[i]=1; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==0 && w[ik]==1 && b[j]==1 && b[k]==1 && w[ji]==1 && w[ki]==1 -> b[i]=0; w[ij]=0; w[ik]=1; }
  :: atomic { b[i]==1 && w[ij]==1 && w[ik]==0 && b[j]==1 && b[k]==1 && w[ji]==1 && w[ki]==1 -> b[i]=0; w[ij]=1; w[ik]=0; }
  od;
#undef ij
#undef j
#undef ji
#undef ik
#undef k
#undef ki
}

#undef if
#undef then
#undef else

#if 0  /* Write this yourself (the default is a coloring).*/
ltl {
  <> [] (b[0]!=b[1] && b[1]!=b[2] && b[2]!=b[3] && b[3]!=b[4] && b[4]!=b[0])
}
#endif

