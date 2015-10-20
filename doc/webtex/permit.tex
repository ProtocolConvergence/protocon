

\title{Action Syntax}
%\author{}
\date{}

\begin{document}
\tableofcontents

\section{Self-Loop Removal (\ilcode{-=>})}

The \ilcode{-=>} operator can be used in place of \ilcode{-->} to automatically remove transitions that would result in a self-loop.
This often helps with readability.
For example, the following two actions are equivalent:
\begin{code}
( x[i-1]==1 && x[i+1]==1 -=> x[i]:=2; )
( x[i-1]==1 && x[i]!=2 && x[i+1]==1 --> x[i]:=2; )
\end{code}

\section{Disallowing Actions (\ilcode{permit} / \ilcode{forbid})}

The \ilcode{permit} and \ilcode{forbid} keywords are used to specify the forms of allowed and disallowed actions available to synthesis.
If \ilcode{permit} does not appear, then it is equivalent to permitting all actions.
If \ilcode{forbid} appears, then the specified form may not be used, even if it matches a \ilcode{permit} statement.

\quicksec{Dining philosophers}
Let us look at the \href{\examplespec/DiningPhilo.prot}{Dining Philosophers Problem} specification, which uses three \ilcode{permit}/\ilcode{forbid} statements.
For this analysis, we only need to know that each philosopher \ilcode{P[i]} can write three binary variables: \ilcode{hungry[i]}, \ilcode{chopstick[L]}, and \ilcode{chopstick[R]} that denote whether the philosopher is hungry, has the chopstick to eir left, and has the chopstick to eir right.

The predicate \ilcode{HasChopsticks} evaluates to true \textiff the philosopher has both chopsticks.

The first action constraint allows actions where \ilcode{hungry[i]} remains constant.
\begin{code}
permit: ( 1==1 --> hungry[i]; );
\end{code}
This uses the shorthand \ilcode{hungry[i];} in place of \ilcode{hungry[i]:=hungry[i];}.
Since neither of the chopstick variables are mentioned in the assignment, they may be changed in any way (without violating a \ilcode{forbid} constraint).
This behavior differs from the syntax of normal actions, where unassigned variables are assumed to stay constant.

The second action constraint allows actions that change \ilcode{hungry[i]} to $0$ while keeping both chopsticks.
\begin{code}
permit: ( HasChopsticks && hungry[i]==1 --> hungry[i]:=0; _; );
\end{code}
This uses the shorthand \ilcode{_;} to keep the unlisted variables at the same values; i.e., \ilcode{chopstick[L]:=chopstick[L]; chopstick[R]:=chopstick[R];}.

The final action constraint disallows actions that change both chopstick variables at the same time.
\begin{code}
forbid: ( 1==1 --> chopstick[L]:=1-chopstick[L]; chopstick[R]:=1-chopstick[R]; );
\end{code}
Note that since \ilcode{hungry[i]} is not assigned, cases where the variable stays the same or is changed are both forbidden.
However, since only the first \ilcode{permit} statement allows chopsticks to change, we are only constraining actions where \ilcode{hungry[i]} does not change.

\quicksec{Self-disabling processes}
When using \ilcode{permit} or \ilcode{forbid}, synthesis may find a protocol where processes are not self-disabling.
This is necessary for the dining philosophers because a philosopher must be able to perform multiple actions in sequence: pick up a chopstick, pick up the other, finish being hungry, set down a chopstick, and set down the other.
However, you may wish to use \ilcode{permit} and \ilcode{forbid} to give hints to synthesis.
In this case, use the \ilkey{-disabling} flag to enforce self-disabling processes.

\section{Randomizing Variables (\ilcode{x[i]:=_;})}

When a variable is marked with \ilcode{random write}, it is assigned randomly by a process without violating safety constraints (e.g., closure).
In the \href{\examplesoln/ColorUniRing.prot}{unidirectional ring coloring} protocol, the following action is used to randomly select a value for \ilcode{x[i]} that differs from \ilcode{x[i-1}.
\begin{code}
( x[i-1]==x[i] --> x[i]:=_; )
\end{code}
Note that this process is self-disabling in the sense that it \textit{can} disable itself by picking certain random values.

\end{document}

