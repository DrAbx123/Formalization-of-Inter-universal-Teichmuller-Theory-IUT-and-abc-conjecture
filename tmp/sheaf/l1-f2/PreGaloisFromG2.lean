import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory

/-!
# PreGaloisCategory from the explicit G2 hypothesis

The terminal, pullback, finite-coproduct and mono-direct-summand fields for
FiniteEtaleCover (curveScheme K) are already proved in
Example36CurveGaloisCategory. This file assembles them with an explicit G2
hypothesis (finite-group action colimits) into a PreGaloisCategory instance.

The G2 field is an explicit parameter, not a new axiom or a sorry. No production
file is modified.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.L1F2PreGaloisFromG2

universe u

open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-- Assemble PreGaloisCategory for the curve cover category from the already
proved G1/G2/G3 fields and an explicit G2 quotient hypothesis. -/
noncomputable def curvePreGaloisCategoryOfG2
    (K : Type u) [Field K]
    (hG2 : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K))) :
    PreGaloisCategory (FiniteEtaleCover (curveScheme K)) where
  hasTerminal := curveAffineEtaleCovers_hasTerminal K
  hasPullbacks := finiteEtaleCoverHasPullbacks (curveScheme K)
  hasFiniteCoproducts := finiteEtaleCover_hasFiniteCoproducts (S := curveScheme K)
  hasQuotientsByFiniteGroups := fun G _ _ => hG2 G
  monoInducesIsoOnDirectSummand := fun {X Y} i _ =>
    finiteEtaleCover_monoInducesIsoOnDirectSummand (S := curveScheme K) i

/-- The explicit G2 hypothesis is exactly the remaining-fields G2 field. -/
noncomputable def curvePreGaloisCategoryOfRemainingFields
    (K : Type u) [Field K]
    (h : CurvePreGaloisCategoryRemainingFields (curveScheme K)) :
    PreGaloisCategory (FiniteEtaleCover (curveScheme K)) :=
  curvePreGaloisCategoryOfG2 K h.hasQuotientsByFiniteGroups

/-- The PreGaloisCategory package together with the exact G2 input it still
needs. This is a statement-level consumer record; the G2 premise is explicit. -/
theorem curvePreGaloisCategoryOfG2_spec
    (K : Type u) [Field K]
    (hG2 : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K))) :
    PreGaloisCategory (FiniteEtaleCover (curveScheme K)) :=
  curvePreGaloisCategoryOfG2 K hG2

end LeanFormal.IUT.Foundations.AlgebraicGeometry.L1F2PreGaloisFromG2
