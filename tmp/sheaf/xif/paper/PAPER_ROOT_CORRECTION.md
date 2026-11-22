# PAPER ROOT CORRECTION (S418 audit)

## Source facts (IUT I Example 3.2(iv), lines 3701-3732)

  q_v is the q-parameter of E_v/K_v.
  q_v is regarded as an element of O^tri(T_X_v), and the text states
  O^tri(T_X_v) is CONGRUENT TO O^tri_{K_v}.
  Here O^tri_{K_v} is the multiplicative monoid of nonzero integral
  elements of K_v (notation lines 252-255).

  By the 2-torsion assumption (Definition 3.1(b)) and the definition of K
  (Definition 3.1(c)), q_v admits a 2l-th root IN O^tri(T_X_v)
  (= O^tri_{K_v}).

  The theta value is q_v^(1/2l) in O^tri(T_X_v), determined up to mu_{2l}.

## Consequence

The paper does NOT define a separate O^tri/root-stack structural-sheaf carrier
at these locations.  The root is an element of the monoid of nonzero integral
elements of K_v, not a root-stack class.  Definition 5.2(ii) defines the
F^vdash-prime-strip, not O^tri.

Therefore:

1. The previous O^tri/root-stack route is not the paper object at this point.
2. S342 proves that the REPO qVFamily has no completion 2l-th root because its
   order is coprime to l.  If the paper asserts the root exists, then REPO
   qVFamily is NOT the paper q_v (or is the wrong q object).
3. The correct paper carrier is the monoid O^tri_{K_v} of nonzero integral
   elements of K_v, with qSection = q_v, rootSection = q_v^(1/2l), and mu_{2l}
   multiplication action.

## Required next check

1. Identify how q_v is constructed in the repo and whether it is qVFamily.
2. Check the 2-torsion/K input: it must force 2l | ord_v(q_v), contradicting
   the repo qVFamily order coprime l.
3. If qVFamily is not q_paper, do not use S342 to rule out the paper root;
   instead construct the paper q_v and its root in O^tri_{K_v}.

## Invalid as paper root carriers

All previous O^tri/root-stack/action-groupoid/function-monoid carriers are
not the object defined at IUT I Example 3.2(iv).  They may be auxiliary models
but must not be used as the paper O^tri.

## Resolution: qVFamily is not paper q_v

qVFamily is the Clause B `SourceTateComparisonWitness.parameter` at an
F-place `(nativeBadLift T).lift b`, with `order_coprime` built into the
witness.  Its `order` is the completion valuation exponent.  It is a source
q-parameter with order coprime to l, NOT the paper K-side q_v.

The paper q_v is a K-side Tate q-parameter for which 2-torsion/K give a
2l-th root in O^tri(T_X_v).  The repo has no identification
`qVFamily = paper q_v`; indeed the order conditions are incompatible.

Consequences:
- S342 rules out a completion 2l-root for qVFamily only.
- It does NOT rule out the paper root for paper q_v.
- QPilotClassicalLog (built from qVFamily) is a native Clause B candidate,
  not the paper q-pilot log.
- O^tri/root-stack is still not the paper object; the paper root is an
  integral element of O^tri_{K_v}.
- All qVFamily->paper q identifications are exact missing.
