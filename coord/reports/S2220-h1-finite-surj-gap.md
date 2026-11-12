# S2220: H^1 finiteness/surjectivity gap

Date: 2026-11-02. Layer O. Consumer: S2214 / S2204 / S2145 / S2114.

## File

tmp/sheaf/xif/paper/S2220H1FiniteSurjActual.lean
Source SHA256 2f696501ffe550bba39d6dd091b4ed7f124c26fcdb3a3e59b4d8ab985b0c3918
olean SHA256 d6eabb4b85aa7584106cc5617147511d6adc001b354f279d46bf410010025301
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Recorded exact missing

S2220FiniteQuotientAction n: a finite quotient Q of G_v through which the
action on mu_{n!} factors (q : G ->* Q surjective, actionQ, compat).
S2220H1FiniteRequired: forall n, Finite (H1(G_v,mu_{n!})).
S2220H1SurjectiveRequired: forall n, Surjective (S2214H1PushforwardHom n).

## Attempt / block

A route to finiteness is the finite quotient: the action on finite mu_{n!}
factors through a finite quotient, and for finite Q the continuous 1-cocycles
inject into all functions Q -> mu_{n!}, so H1 is finite.  The finite quotient
action and its finiteness theorem were not completed: Lean instance elaboration
for the quotient's Group/TopologicalSpace/IsTopologicalGroup data in the
structure signature blocked the construction.  The remaining input is the
actual finite quotient and the H1 comparison
H1(G_v,mu_{n!}) ~ H1(Q,mu_{n!}).

No finiteness or surjectivity is claimed.
