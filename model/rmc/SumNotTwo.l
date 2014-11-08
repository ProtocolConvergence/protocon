
let

x :: {0, 1, 2}

copy(i) = (x[i] = x'[i])
copy_other(i) = (all1 j ((j = i) | copy(j)))

adjacent(i,j) = ((j = i+1) | ((j = 0) & (i = $)))

legit(i) =
  (ex1 pd
      adjacent(pd,i)
    & ~((x[pd] = '0') & (x[i] = '2'))
    & ~((x[pd] = '1') & (x[i] = '1'))
    & ~((x[pd] = '2') & (x[i] = '0'))
  )
invariant = (all1 i legit(i))

delta(pd,i) =
  (  (x[pd] = '0') & (x[i] = '2') & (x'[i] = '0')
   | (x[pd] = '1') & (x[i] = '1') & (x'[i] = '0')
   | (x[pd] = '2') & (x[i] = '0') & (x'[i] = '1')
  )

act(i) =
  (copy_other(i) &
   (ex1 pd adjacent(pd,i) & delta(pd,i))
  )

some_xn = (ex1 i act(i))

#initial = (ex1 i ((i = 0) & (x[i] = '0') | (x[i] = '1') | (x[i] = '2')))
#size_cond = ~(ex1 i adjacent(i,i))
#size_cond = ~(ex1 i ex1 j adjacent(i,j) & adjacent(j,i))
#size_cond = (ex1 i ex1 j ex1 k adjacent(i,j) & adjacent(j,k) & ~adjacent(k,i))

deadlock = (~invariant() & ~guard(some_xn()))

bad_shadow = (invariant() & some_xn())

unsafe = (deadlock() | bad_shadow())

livelock = (alw some_xn())

in
(
  #unsafe()
  livelock()
)

