# S2532 transport actual + non-monic residue repair plan

Date: 2026-11-03.

## ACTUAL

tmp/sheaf/xif/paper/S2532PairTransitiveActual.lean
  src EA0626977994385F2E24CF6F54488CD47F767989DCFA2662ABB73313F6626B9B
  olean B7EC2E21FF8BF4AD0379436DD948DF572F0BF7A3E16485DDE6BACDF370FAD80F, 162544 B
  EXIT=0, axioms propext/Classical.choice/Quot.sound, no sorryAx.
  S2532RootToRangeTransport : S2470RootToRangeTransport.

## Monic datum obstruction

S2470ActualResidueData requires f.Monic.  prePsi5 has leading coeff 5 and
constant 5^18/2^36; monic forces f = (1/5)*psi5F over F', so constant is
5^17/2^36.  F' contains i, so 2 is nonunit in O_F' and 1/2 is not integral.
Thus no monic integral model exists and S2470ActualResidueData is empty.

## Non-monic repair

Take the integral non-monic model
  f = S2132Psi5Z.map (Int.castRingHom (RingOfIntegers S1720Field)).
Its rational base change is expected to be 2^36 * S2057Psi5Q, so
  f.map (algebraMap O_F' F') = C (2^36) * S2057Psi5F.
S2540 gives Irreducible (S2132Psi5Z mod 613); S2481 proves the defining
polynomial of F' splits completely mod 613, so there is a residue-degree-one
prime p above 613 and O_F'/p ~= ZMod 613.  Then fbar f p is S2132Psi5Z mod 613
up to the residue-field isomorphism, hence irreducible of degree 12;
separability follows from char 613 and degree 12 / derivative nonzero.
Splitting over the 5-division field and the root card 12 are formal.

The remaining transport to S2532Target must use a NON-MONIC Dedekind-Frobenius
variant.  S2532RootToRangeTransport itself does not use f.Monic; only S2470's
S2470_residueIrreducible_rootTwelveCycle does (for fbar monic and S2440).
At p above 613 the leading coefficient 5*2^36 is a unit, so fbar can be
normalized to monic by a unit of the residue field; root sets, permBar and
frobBar are unchanged by nonzero scalar scaling.  Formal missing:

1. prove S2132Psi5Z.map Q = 2^36 * S2057Psi5Q (coefficientwise from
   S1942_preΨ_five, or a dedicated certificate);
2. construct a residue-degree-one prime p of F' above 613 from
   S2481HMod613_splits, and P above p;
3. prove scaling-invariance of rootSet/permBar/frobBar for nonzero scalar
   multiples, and adapt S2470's irreducible residue theorem to fbar monic
   after scaling;
4. feed the non-monic root twelve-cycle into S2532RootToRangeTransport
   (drop the unused hmonic argument).

None of 1-4 is in the tree today.  This is the precise repair path; it does
not weaken the target semantics: the same S2440TwelveCycleInputRequired and
S2532Target are produced, only the integral model is allowed non-monic.

## Status

- transport ACTUAL; monic residue datum obstructed; non-monic path specified.
- no fake; no sorryAx.
