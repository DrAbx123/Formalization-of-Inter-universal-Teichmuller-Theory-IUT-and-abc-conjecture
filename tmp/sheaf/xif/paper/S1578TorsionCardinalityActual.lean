import tmp.sheaf.xif.paper.S1564GaussianTorsionBasisActual
import tmp.sheaf.xif.paper.S1362PrePsiSeparabilityActual
import tmp.sheaf.xif.paper.S1431MulByIntDegreeActual

/-! # S1578: Gaussian l-torsion cardinality: exact first missing

S1564 reduces `GaussianTorsionBasis` to
  S1564TorsionCardinalityExact l : Nat.card ((GaussianCurve l).LTorsion l) = l^2.

This file records the actual reduction and the exact first missing fields.

## What is actual

* S1362 proves, under the S1329 group-law criterion, the exact equivalence
  between the polynomial separability gap `S1362PreΨSeparabilityGap l` and
  the l-torsion cardinality gap `S1362LTorsionCardinalityGap l`.
* S1431 proves `degree_mulByIntIsogeny`: the function-field degree of [n] is
  n^2 (with the coprime/separability hypotheses).

## What is still missing (not actual)

1. `S1329ConcreteCriterion l`: the division-polynomial group-law criterion
   for the concrete Gaussian curve.  It is a `Prop` definition, no inhabitant.
2. `S1362PreΨSeparabilityGap l` (equivalently `S1362RootCount l`):
   separability/root count of the concrete `prePsi_l`.  It is a `Prop`
   definition, no inhabitant.
3. A bridge from S1431's function-field `degree_mulByIntIsogeny = n^2` to
   the cardinality of the actual point kernel / `LTorsion` over the algebraic
   closure.  S1431 gives the function-field degree only; no point-kernel
   cardinality theorem is in the tree.

Therefore the Gaussian torsion cardinality is NOT proved here; the exact
first missing fields are items 1 and 2, plus bridge item 3 if the S1431 route
is used.  No arbitrary basis/Nonempty gate is introduced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1578TorsionCardinalityActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1564GaussianTorsionBasisActual
open LeanFormal.IUT.XiFPaper.S1362PrePsiSeparabilityActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual

variable {l : PrimeGeFive}

/-- Exact first missing field 1: the concrete division-polynomial group-law
criterion. -/
abbrev S1578ConcreteCriterionExact (l : PrimeGeFive) : Prop :=
  S1329ConcreteCriterion l

/-- Exact first missing field 2: the concrete prePsi separability gap. -/
abbrev S1578SeparabilityGapExact (l : PrimeGeFive) : Prop :=
  S1362PreΨSeparabilityGap l

/-- Actual reduction: criterion plus separability gap gives the frozen
l-torsion cardinality gap, exactly as proved in S1362. -/
theorem s1578CardinalityGap_of_criterion_and_separability
    (hcrit : S1578ConcreteCriterionExact l)
    (hgap : S1578SeparabilityGapExact l) :
    S1362LTorsionCardinalityGap l :=
  (s1362Gap_equiv_of_criterion l hcrit).mp hgap

/-- The same conclusion via the S1362 root-count form. -/
theorem s1578CardinalityGap_of_criterion_and_rootCount
    (hcrit : S1578ConcreteCriterionExact l)
    (hroot : S1362RootCount l) :
    S1362LTorsionCardinalityGap l :=
  (s1362Gap_equiv_of_criterion l hcrit).mp
    ((s1362RootCount_iff_separable l).mp hroot)

/-- Exact missing type: S1564's Gaussian curve torsion cardinality. -/
abbrev S1578GaussianTorsionCardinalityExact (l : PrimeGeFive) : Prop :=
  S1564TorsionCardinalityExact l

end LeanFormal.IUT.XiFPaper.S1578TorsionCardinalityActual

end
