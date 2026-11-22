import tmp.sheaf.xif.paper.S1544LTorsionKernelFieldActual
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-! # S1564: Gaussian l-torsion rank two / basis: conditional and exact

For the actual Gaussian curve of S1544, `GaussianTorsionBasis l` is
  (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] (GaussianCurve l).LTorsion l.

## Conditional rank-two

If the actual l-torsion is a finite ZMod-l-module with `Nat.card = l^2`, then
`Module.finrank = 2` and `Module.finBasisOfFinrankEq` gives an actual basis
and the required linear equivalence.  This part is proved below.

## Exact first missing field

The hypothesis `Nat.card ((GaussianCurve l).LTorsion l) = l.value ^ 2` is not
available as an imported theorem: the actual cardinality proof exists only in
`_S1405Probe3.lean` (not a built module), conditional on
`S1329ConcreteCriterion l` and `S1362RootCount l`.  The exact first missing
module is that built cardinality/finiteness theorem.  No arbitrary basis,
`FiniteDimensional.finBasis` without the cardinality input, or Nonempty gate is
used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1564GaussianTorsionBasisActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1544LTorsionKernelFieldActual

variable {l : PrimeGeFive}
variable [Fact l.value.Prime]

/-- Exact missing cardinality input. -/
def S1564TorsionCardinalityExact (l : PrimeGeFive) : Prop :=
  Nat.card ((GaussianCurve (l := l)).LTorsion l) = l.value ^ 2

/-- Conditional rank-two: cardinality plus finite module structure forces
`finrank = 2`. -/
theorem s1564_finrank_eq_two
    [Module.Finite (ZMod l.value) ((GaussianCurve (l := l)).LTorsion l)]
    (hcard : S1564TorsionCardinalityExact (l := l)) :
    Module.finrank (ZMod l.value) ((GaussianCurve (l := l)).LTorsion l) = 2 := by
  have hnat := Module.natCard_eq_pow_finrank (K := ZMod l.value)
    (V := (GaussianCurve (l := l)).LTorsion l)
  have hnat' : Nat.card ((GaussianCurve (l := l)).LTorsion l) =
      l.value ^ Module.finrank (ZMod l.value)
        ((GaussianCurve (l := l)).LTorsion l) := by
    simpa [Nat.card_zmod] using hnat
  have hpow : l.value ^ 2 = l.value ^
      Module.finrank (ZMod l.value) ((GaussianCurve (l := l)).LTorsion l) := by
    rw [← hcard]
    exact hnat'
  have h0 : 0 < l.value := l.prime.pos
  have h1 : l.value ≠ 1 := l.prime.ne_one
  exact (pow_right_injective₀ h0 h1).eq_iff.mp hpow.symm

/-- Actual basis from the conditional finrank: `Module.finBasisOfFinrankEq`. -/
noncomputable def s1564BasisOfCard
    [Module.Finite (ZMod l.value) ((GaussianCurve (l := l)).LTorsion l)]
    [Module.Free (ZMod l.value) ((GaussianCurve (l := l)).LTorsion l)]
    (hcard : S1564TorsionCardinalityExact (l := l)) :
    Module.Basis (Fin 2) (ZMod l.value) ((GaussianCurve (l := l)).LTorsion l) :=
  Module.finBasisOfFinrankEq (ZMod l.value)
    ((GaussianCurve (l := l)).LTorsion l) (s1564_finrank_eq_two hcard)

/-- Conditional GaussianTorsionBasis from the actual basis. -/
noncomputable def s1564GaussianTorsionBasisOfCard
    [Module.Finite (ZMod l.value) ((GaussianCurve (l := l)).LTorsion l)]
    [Module.Free (ZMod l.value) ((GaussianCurve (l := l)).LTorsion l)]
    (hcard : S1564TorsionCardinalityExact (l := l)) :
    GaussianTorsionBasis l :=
  (s1564BasisOfCard hcard).equivFun.symm

end LeanFormal.IUT.XiFPaper.S1564GaussianTorsionBasisActual

end
