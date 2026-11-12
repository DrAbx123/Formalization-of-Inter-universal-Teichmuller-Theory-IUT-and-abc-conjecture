# S2532 transport actual + S2470ActualResidueData obstruction

Date: 2026-11-03. Serial -j1.

## Actual

tmp/sheaf/xif/paper/S2532PairTransitiveActual.lean
  src SHA EA0626977994385F2E24CF6F54488CD47F767989DCFA2662ABB73313F6626B9B
  EXIT=0
  olean SHA B7EC2E21FF8BF4AD0379436DD948DF572F0BF7A3E16485DDE6BACDF370FAD80F
  size 162544
  axioms propext, Classical.choice, Quot.sound.

S2532RootToRangeTransport : S2470RootToRangeTransport is ACTUAL.

## Residue data obstruction (precise, not yet formalized)

S2470ActualResidueData requires a MONIC f over O_{F'} with
  f.map F' = C c * S2057Psi5F,  c != 0.

Leading coefficient: prePsi_5 = prePsi_4 * Psi2Sq^2 - Psi3^3 has leading
coefficient 2*16 - 27 = 5; constant coefficient is 5^18/2^36
(S2132Psi5Q_eval_zero).  Hence monic forces c = 1/5 and

  f.coeff 0 maps to (1/5)*(5^18/2^36) = 5^17/2^36.

Now F' = SplittingField(S1687H * (X^2+1)) contains i.  In O_{Q(i)}, 2 is
nonunit (2 = -i(1+i)^2), and extension cannot make it a unit; hence 1/2 is
not integral in F'.  Therefore f.coeff 0 = 5^17/2^36 would have to lie in
O_{F'}, impossible.  More elementarily, if x = f.coeff 0 in O_{F'} maps to
5^17/2^36, then 2^36 x = 5^17; but (2,5)=1 in O_{F'} and 2 does not divide 5.

Conclusion: S2470ActualResidueData is UNINHABITABLE in the current
definition, because the required monic integral model of a nonzero multiple
of psi_5 does not exist.  Consequently S2532ResidueCertificateRequired
(= Nonempty S2470ActualResidueData) is false, and the mod-613/degree-12
twelve-cycle route cannot produce the target through this structure.

A formal Lean proof still needs: leading coefficient of prePsi_5, integrality
of 2 in F' (i in F'), and the divisibility contradiction.  These are arithmetic
lemmas, not a transport gap.

## Consequence

The pair-transitivity route now needs a different arithmetic datum: a
NON-monic integral model / fractional ideal formulation, or a prime in an
extension where the roots are integral, not the current S2470ActualResidueData.
The S2132 (2,10) cycle-type route is separate (volumedet / two-factor
certificate).

## Status

- root-to-range transport: ACTUAL.
- residueData: precise obstruction; no inhabitant.
- no fake; no sorryAx.
