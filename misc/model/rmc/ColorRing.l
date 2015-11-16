
let

x :: {0, 1, 2}

copy(i) = (x[i] = x'[i])
copy_other(i) = (all1 j ((j = i) | copy(j)))

adjacent(i,j) = ((j = i+1) | ((j = 0) & (i = $)))

legit(i) =
  (ex1 pd ex1 sc
      adjacent(pd,i) & adjacent(i,sc)
    & ~(x[pd] = x[i])
    & ~(x[i] = x[sc])
  )
invariant = (all1 i legit(i))

delta(pd,i,sc) =
  (  ( (x[pd] = '0') & (x[i] = '0') & (x[sc] = '0') & (x'[i] = '1') )
   | ( (x[pd] = '0') & (x[i] = '0') & (x[sc] = '1') & (x'[i] = '2') )
   | ( (x[pd] = '0') & (x[i] = '0') & (x[sc] = '2') & (x'[i] = '1') )
   | ( (x[pd] = '0') & (x[i] = '1') & (x[sc] = '1') & (x'[i] = '2') )
   | ( (x[pd] = '0') & (x[i] = '2') & (x[sc] = '2') & (x'[i] = '1') )
   | ( (x[pd] = '1') & (x[i] = '0') & (x[sc] = '0') & (x'[i] = '2') )
   | ( (x[pd] = '1') & (x[i] = '1') & (x[sc] = '0') & (x'[i] = '2') )
   | ( (x[pd] = '1') & (x[i] = '1') & (x[sc] = '1') & (x'[i] = '2') )
   | ( (x[pd] = '1') & (x[i] = '1') & (x[sc] = '2') & (x'[i] = '0') )
   | ( (x[pd] = '1') & (x[i] = '2') & (x[sc] = '2') & (x'[i] = '0') )
   | ( (x[pd] = '2') & (x[i] = '0') & (x[sc] = '0') & (x'[i] = '1') )
   | ( (x[pd] = '2') & (x[i] = '1') & (x[sc] = '1') & (x'[i] = '0') )
   | ( (x[pd] = '2') & (x[i] = '2') & (x[sc] = '0') & (x'[i] = '1') )
   | ( (x[pd] = '2') & (x[i] = '2') & (x[sc] = '1') & (x'[i] = '0') )
   | ( (x[pd] = '2') & (x[i] = '2') & (x[sc] = '2') & (x'[i] = '0') )
  )

act(i) =
  (copy_other(i) &
   (ex1 pd ex1 sc adjacent(pd,i) & adjacent(i,sc) & delta(pd,i,sc))
  )

some_xn = (ex1 i act(i))

size_cond = ~(ex1 i ex1 j (i = j) & adjacent(i,j))

deadlock = (~invariant() & ~guard(some_xn()))

bad_shadow = (invariant() & some_xn())

unsafe = (deadlock() | bad_shadow())

livelock = (alw some_xn())

in
(
  size_cond() &
  #unsafe()
  livelock()
)

