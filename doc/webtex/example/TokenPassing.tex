
\title{Token Passing}
%\author{}
\date{}

\begin{document}


Token passing systems are used for distributed mutual exclusion, where exactly one process has a \textit{token} at any given time, and the token must be passed in order for other processes to have this privilege.
In the context of self-stabilization, the system may be in a state with multiple tokens, and it therefore must converge to having a single token.

\tableofcontents

\section{Dijkstra's Token Ring}
\label{sec:TokenRingDijkstra}

\quicksec{TokenRingDijkstra}
(\href{\examplespec/TokenRingDijkstra.prot}{spec},
\href{\examplesett/TokenRingDijkstra.prot}{args},
\href{\examplesoln/TokenRingDijkstra.prot}{soln})

\section{5-State Token Ring}
\label{sec:TokenRingFiveState}

\quicksec{TokenRing}
(\href{\examplespec/TokenRing.prot}{spec},
\href{\examplesett/TokenRingFiveState.args}{args},
\href{\examplesynt/TokenRingFiveState.prot}{synt},
\href{\examplesoln/TokenRingFiveState.prot}{soln} )

This is a unidirectional token ring that has 5 states per process.
Without using randomization, no smaller token ring exists.
Interestingly, we can still pass a token with every action in the invariant.

\section{6-State Token Ring}
\label{sec:TokenRingSixState}

\quicksec{TokenRingSixState}
(\href{\examplespec/TokenRingSuperpos.prot}{spec},
\href{\examplesett/TokenRingSixState.args}{args},
\href{\examplesynt/TokenRingSuperpos.prot}{synt},
\href{\examplesoln/TokenRingSixState.prot}{soln})

\section{3-Bit Token Ring}
\label{sec:TokenRingThreeBit}

\quicksec{TokenRingThreeBit}
(\href{\examplespec/TokenRingThreeBit.prot}{spec},
\href{\examplesett/TokenRingThreeBit.args}{args},
\href{\examplesynt/TokenRingThreeBit.prot}{synt},
\href{\examplesoln/TokenRingThreeBit.prot}{soln})

This section shows how to synthesize a self-stabilizing token ring using the same topology given by
Gouda and Haddix in \textit{The Stabilizing Token Ring in Three Bits}.
It uses 8 states per process.
Not every action in the invariant passes a token, which causes a noticeable lag for larger rings.

\subsection{Problem Instance}

\codeinputlisting{../../../examplespec/TokenRingThreeBit.prot}

Each process can read \ttvbl{e[i-1]} and \ttvbl{t[i-1]} and can write \ttvbl{e[i]}, \ttvbl{t[i]}, and \ttvbl{ready[i]}.
There is a distinguished process \ttvbl{Bot} that can act differently than the others.

The invariant is specified as all states where exactly one process has a token.
\ttvbl{Bot} is defined to have a token when \ilcode{t[0] == t[N-1]} and each other \ttvbl{P} process has a token when \ilcode{t[i] != t[i-1]}.

With the shadow actions, we enforce that processes act like Dijkstra's token ring on one bit (the \ttvbl{t} variables).

\subsection{Synthesis}

Let's try to find a stabilizing token ring using three bits on a ring of size $5$.
\begin{code}
protocon -x examplespec/TokenRingThreeBit.prot -o tmp/3bit.prot -def N 5
\end{code}

Is the protocol stabilizing on a ring of size $3$?
\begin{code}
protocon -verify -x tmp/3bit.prot -def N 3
\end{code}

How about of size $4$ or $6$?
\begin{code}
protocon -verify -x tmp/3bit.prot -def N 4
protocon -verify -x tmp/3bit.prot -def N 6
\end{code}

Probably not.
Let's try again, taking those sizes into account!
\begin{code}
protocon -x examplespec/TokenRingThreeBit.prot -o tmp/3bit.prot -def N 5 -param N 3 -param N 4 -param N 6
\end{code}

But what if we want to search up to size $7$, but it takes too long check a system of that size at each decision level?
Use the \ilflag{-no-partial} flag to just verify the protocol on that system after finding a protocol that is self-stabilizing for all smaller sizes.
\begin{code}
protocon -x examplespec/TokenRingThreeBit.prot -o tmp/3bit.prot -def N 5 -param N 3 -param N 4 -param N 6 -param [ -def N 7 -no-partial ]
\end{code}

\subsection{Stabilizing Version}

\codeinputlisting{../../../examplesoln/TokenRingThreeBit.prot}

\section{3-State Token Ring (Dijkstra)}
\label{sec:TokenRingThreeState}

\quicksec{TokenRingThreeState}
(\href{\examplespec/TokenRingThreeState.prot}{spec},
\href{\examplesett/TokenRingThreeState.args}{args},
\href{\examplesynt/TokenRingThreeState.prot}{synt},
\href{\examplesoln/TokenRingThreeState.prot}{soln})

This ring is bidirectional, and passes the token back-and-forth.
Every action in the invariant passes a token.

\section{3-State Token Chain}
\label{sec:TokenChainThreeState}

\quicksec{TokenChainThreeState}
(\href{\examplespec/TokenChain.prot}{spec},
\href{\examplesett/TokenChainThreeState.args}{args},
\href{\examplesynt/TokenChain.prot}{synt},
\href{\examplesoln/TokenChainThreeState.prot}{soln})

This is a bidirectional chain that passes the token back-and-forth.
It uses 3 states per process.
Not every action in the invariant passes a token, but the actions that do not pass the token can be run in parallel with the token-passing ones, so the performance hit is small.


\section{4-State Token Chain (Dijkstra)}
\label{sec:TokenChainDijkstra}

\quicksec{TokenChainDijkstra}
(\href{\examplespec/TokenChainDijkstra.prot}{spec},
\href{\examplesynt/TokenChainDijkstra.prot}{synt},
\href{\examplesoln/TokenChainDijkstra.prot}{soln})

This is a bidirectional chain that passes the token back-and-forth.
It uses 4 states per process.
It converges quickly and every action in the invariant passes the token.


\end{document}

