
# Action Syntax

## Self-Loop Removal (`-=>`)

The `-=>` operator can be used in place of `-->` to automatically remove transitions that would result in a self-loop.
This often helps with readability.
For example, the following two actions are equivalent:
```
( x[i-1]==1 && x[i+1]==1 -=> x[i]:=2; )
( x[i-1]==1 && x[i]!=2 && x[i+1]==1 --> x[i]:=2; )
```

## Disallowing Actions (`permit` / `forbid`)

The `permit` and `forbid` keywords are used to specify the forms of allowed and disallowed actions available to synthesis.
If `permit` does not appear, then it is equivalent to permitting all actions.
If `forbid` appears, then the specified form may not be used, even if it matches a `permit` statement.

**Dining philosophers.**
Let us look at the [Dining Philosophers Problem](../examplespec/DiningPhilo.prot) specification, which uses three `permit`/`forbid` statements.
For this analysis, we only need to know that each philosopher `P[i]` can write three binary variables: `hungry[i]`, `chopstick[L]`, and `chopstick[R]` that denote whether the philosopher is hungry, has the chopstick to eir left, and has the chopstick to eir right.

The predicate `HasChopsticks` evaluates to true \textiff the philosopher has both chopsticks.

The first action constraint allows actions where `hungry[i]` remains constant.
```
permit: ( 1==1 --> hungry[i]; );
```
This uses the shorthand `hungry[i];` in place of `hungry[i]:=hungry[i];`.
Since neither of the chopstick variables are mentioned in the assignment, they may be changed in any way (without violating a `forbid` constraint).
This behavior differs from the syntax of normal actions, where unassigned variables are assumed to stay constant.

The second action constraint allows actions that change `hungry[i]` to 0 while keeping both chopsticks.
```
permit: ( HasChopsticks && hungry[i]==1 --> hungry[i]:=0; _; );
```
This uses the shorthand `_;` to keep the unlisted variables at the same values; i.e., `chopstick[L]:=chopstick[L]; chopstick[R]:=chopstick[R];`.

The final action constraint disallows actions that change both chopstick variables at the same time.
```
forbid: ( 1==1 --> chopstick[L]:=1-chopstick[L]; chopstick[R]:=1-chopstick[R]; );
```
Note that since `hungry[i]` is not assigned, cases where the variable stays the same or is changed are both forbidden.
However, since only the first `permit` statement allows chopsticks to change, we are only constraining actions where `hungry[i]` does not change.

**Self-disabling processes.**
When using `permit` or `forbid`, synthesis may find a protocol where processes are not self-disabling.
This is necessary for the dining philosophers because a philosopher must be able to perform multiple actions in sequence: pick up a chopstick, pick up the other, finish being hungry, set down a chopstick, and set down the other.
However, you may wish to use `permit` and `forbid` to give hints to synthesis.
In this case, use the `-disabling` flag to enforce self-disabling processes.

## Randomizing Variables (`x[i]:=_;`)

When a variable is marked with `random write`, it is assigned randomly by a process without violating safety constraints (e.g., closure).
In the [unidirectional ring coloring](../examplesoln/ColorUniRing.prot) protocol, the following action is used to randomly select a value for `x[i]` that differs from `x[i-1`.
```
( x[i-1]==x[i] --> x[i]:=_; )
```
Note that this process is self-disabling in the sense that it *can* disable itself by picking certain random values.

