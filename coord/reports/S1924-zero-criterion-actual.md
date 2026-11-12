# S1924: division-polynomial zero criterion, actually proved

Date: 2026-11-01 (Asia/Shanghai).

File: `tmp/sheaf/xif/paper/S1924ZeroCriterionActual.lean`

## Verification

- Build command:
  `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1924ZeroCriterionActual.olean tmp/sheaf/xif/paper/S1924ZeroCriterionActual.lean`
- EXIT = 0, no errors, no warnings.
- Source SHA256: `93C8F9A00C2F74BBB97F24E48AE53FDE575A7E58BE3D5BCA737BED4D668929FE`
- Source bytes: 13532.
- Olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1924ZeroCriterionActual.olean`
- Olean SHA256: `7E406EC185DDD24E81DA8D40789EC56CE9960D4040E724942894C1DBD575E9E4`
- Olean bytes: 169520.
- Import re-check: `_S1924OleanCheck.lean` imports the olean, `#check`s the main
  declarations and re-runs `#print axioms`; EXIT = 0.
- Axiom footprint of all 16 exported theorems: `propext, Classical.choice,
  Quot.sound` only.  No `sorryAx`, no `axiom`, no `opaque`.

## What is proved

The full group-law criterion, for **every field (with the classical
decidable equality), every Weierstrass curve and every integer n**:

```lean
S1924Criterion_generic (W : WeierstrassCurve F) (n : Z) :
  forall P : W.toAffine.Point, n • P = 0 <-> W.evalDivisionPolynomialAtPoint n P = 0
```

In particular this proves S1361's two missing halves:

- `S1924Detection_generic W n : s1361Detection W n`;
- `S1924ZeroCriterion_generic W n : s1361ZeroCriterion W n`;

and S1329's criterion `S1924DivisionCriterion W l : s1329DivisionCriterion W l`.

Specialised to the actual curve E' of S1906:

- `S1924S1906ZeroCriterion l : S1906ZeroCriterion l`  (this is S1906's (b));
- `S1924S1906Detection l : S1906Detection l`;
- `S1924S1906Criterion l : S1906Criterion l`.

## Proof route (no fake, no new axiom)

The only nontrivial input is the universal multiplication-by-n formula already
proved in S1626:

```lean
s1626ZSMulPointEqSmulEval :
  (n • fromAffine (some x y h)).point = class (phi_n(x,y), omega_n(x,y), psi_n(x,y))
```

This is the TauCeti universal-curve layer ported in S1593--S1626; it is
kernel-checked with the standard axioms.

Two elementary Jacobian facts convert the formula into the criterion.

1. **Detection.**  If `n • P = 0`, the class of the evaluated triple is the
   zero class `class ![1,1,0]`.  Scaling `![1,1,0]` preserves the
   Z-coordinate, so `psi_n(P) = 0`.  This uses
   `Jacobian.Z_eq_zero_of_equiv`.

2. **Zero criterion.**  If `psi_n(P) = 0`, the evaluated triple has Z = 0.
   It is nonsingular: it is a representative of the point class
   `(n • P).toJacobian`, whose nonsingularity is part of the
   `Jacobian.Point` structure; `Jacobian.nonsingularLift_iff` transfers
   this to the representative.  Then `Jacobian.equiv_zero_of_Z_eq_zero`
   puts the representative in the zero class, so `n • P = 0`.

No divisor theory, x-coordinate formula, separability, torsion cardinality or
local analysis is used.  In particular the earlier S1642 concern about
"evaluated nonsingularity" is bypassed: the point formula already gives the
nonsingular lift, and `nonsingularLift_iff` reads off nonsingularity of the
evaluated representative without a ring-level specialization lemma.

## Consequences for S1906

Since both halves of the criterion are now unconditional, S1906's inputs (a)
the x-coordinate formula and (b) the zero criterion are no longer needed for
the rank-two basis gap.  The file proves:

- `S1924S1906NatCard_eq l`:
  `Nat.card E'[l] = 1 + 2 * #roots(prePsi_l)` (unconditional).
- `S1924S1906BasisGap_iff_rootCount l`:
  `S1725RankTwoBasisGap l <-> #roots(prePsi_l) = (l^2 - 1)/2`.
- `S1924S1906RootCount_iff_separable l`:
  the root count is equivalent to `S1906Separability l`.
- `S1924S1906BasisGap_iff_separable l`:
  `S1725RankTwoBasisGap l <-> S1906Separability l`.
- `S1924S1906BasisGap_of_rootCount`,
  `S1924S1906BasisGap_of_separable`,
  `S1924S1906BasisGap_of_genericSeparable`:
  the three consumer forms.
- `S1924S1906NatCard_eq_sq_of_separable`:
  `Nat.card E'[l] = l^2` from separability.
- `S1924S1906TorsionCardinality_iff_separable`.

The exact remaining input is therefore **only** S1906's (c), the
S1366/S1420 characteristic-zero separability of `prePsi_l`.  This file does
not prove it and does not assume it.

## Relation to earlier reports

- S1397/S1486 concluded that the general odd-n zero criterion was missing.
  The present proof shows that S1626's universal formula is exactly the
  missing bridge.
- S1412 (divisor support/degree) is not needed.
- S1642's evaluated-nonsingularity target is not needed in the form stated
  there; the point formula plus `nonsingularLift_iff` suffices.
- S1906's own report remains correct about what was proved there; this file
  supersedes its dependency on (a) and (b) for the basis gap.

## Consumers

Use `S1924S1906BasisGap_of_genericSeparable` (or
`S1924S1906BasisGap_of_separable`) instead of
`S1906BasisGap_of_xCoordinateFormula_zeroCriterion_separable` /
`S1906BasisGap_of_xCoordinateFormula_zeroCriterion_genericSeparable`.
