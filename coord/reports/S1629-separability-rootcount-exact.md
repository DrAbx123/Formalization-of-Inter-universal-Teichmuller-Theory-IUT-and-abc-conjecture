# S1629: Gaussian prePsi separability / root count — exact missing algebraic lemma

Date: 2026-10-31. No Lean file: the first missing lemma is a nonzero
resultant/discriminant, which is exactly S1362PreΨSeparabilityGap.

## 1. Target

S1362PreΨSeparabilityGap l is equivalent to:

- S1362PreΨSeparable l : (S1362PreΨ l).Separable;
- S1362PreΨSquarefree l : Squarefree (S1362PreΨ l);
- S1362RootCount l : roots.toFinset.card = (l^2 - 1)/2;
- S1329ConcreteSeparable l.

S1362 already proves all these equivalences, plus the unconditional degree and
splitting bounds.  What is missing is the single nonzero resultant/discriminant
statement.

## 2. Exact first missing algebraic lemma

The exact first lemma is

  resultant (S1362PreΨ l) (derivative (S1362PreΨ l)) != 0

or equivalently

  discrim (S1362PreΨ l) != 0

for the concrete Gaussian curve over S1362Closure l.

These are equivalent to Separable / Squarefree / root-count via Mathlib's
resultant/discriminant API (Polynomial.separable_iff_resultant_ne_zero,
Polynomial.squarefree_iff_discrim_ne_zero), neither of which is proved for this
specific l-division polynomial.

## 3. Why the existing degree/root bound is insufficient

S1362 already has:

- natDegree prePsi_l = (l^2 - 1)/2;
- prePsi_l splits over the algebraic closure;
- roots.toFinset.card <= (l^2-1)/2.

The reverse inequality needs distinct roots, i.e. separability.  Degree and
splitting alone give only the upper bound; no root lower bound follows without
the nonzero resultant/discriminant.

## 4. S1329ConcreteCriterion

The group-law criterion

  s1329DivisionCriterion W l :
    forall P, (l : Int) • P = 0 <-> evalDivisionPolynomialAtPoint l P = 0

is a separate first missing algebraic/group-law lemma, not a consequence of
separability.  It is the concrete form of the missing ZSMul evaluation bridge
(zsmul_eq_smulEval / division-polynomial zero criterion).  Neither direction is
available for general l in Mathlib v4.32.2.

## 5. Conclusion

- actual: S1362 degree/splitting/upper bound and the equivalences between
  separability, squarefree, root count and S1329ConcreteSeparable.
- exact first missing: nonzero resultant/discriminant of S1362PreΨ l.
- S1329ConcreteCriterion additionally needs the group-law ZSMul bridge.
- No Lean file written: any file would restate the existing S1362 gap; no fake
  separability/criterion; report EXIT=0.
