# S2419: Kummer transition surjectivity

Date: 2026-11-03. Layer O. Consumer: S2214 / S2410 / S2114.

## File

tmp/sheaf/xif/paper/S2419H1SurjLimitActual.lean
Source SHA256 a909cd78c588c23db344510391f14d53e455bdacc1c3a08ec812257c46195060
olean SHA256 3f9d8e88fea9cc7da8382487f9f2f1ef1f1d45c09637ea2cab5e093536883765
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2419QuotTransition_surjective: the Kummer quotient transition
  quotTransition (K := Q_p) h : Q_p^x/(Q_p^x)^n -> Q_p^x/(Q_p^x)^m
is surjective for m ∣ n.
S2419H1Transition_surjective: the external Kummer H^1 transition
  h1Transition (K := Q_p) (Omega := AlgebraicClosure Q_p) h
is surjective for m,n with NeZero (m : Q_p), NeZero (n : Q_p) and m ∣ n,
using kummerEquivAlgClosure and kummerEquiv_quotTransition.

## Exact first missing

S2419H1SurjectiveRequired: the internal transition
  forall n, Surjective (S2214H1PushforwardHom p n).
The external Kummer transition is now actual-surjective; the remaining step is
the alignment square between S2214H1PushforwardHom and h1Transition under
S2410H1Equiv.  No unconditional internal surjectivity is claimed.
