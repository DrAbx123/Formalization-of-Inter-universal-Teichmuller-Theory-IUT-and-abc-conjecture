import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartActionQuotientCompat
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Affine chart overlap compatibility proof

This file packages an actual overlap witness for two local affine quotient
charts and proves the diagonal case.  Nontrivial overlaps require the fixed
localization comparison and are isolated as an explicit Prop, not an
inhabited provider.

Post-compile-delta draft; held for watchdog compilation. No provider/IsColimit.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapCompatProof

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyFromCover
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartActionQuotientCompat
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- An actual overlap witness for two local quotient charts: a common scheme
with open immersions into both charts whose chart maps to the base agree. -/
structure AffineChartOverlapWitness (D₁ D₂ : AffineChartLocalQuotient S) where
  /-- The common overlap scheme. -/
  W : Scheme.{u}
  /-- Open immersion into the first chart. -/
  f₁ : W ⟶ D₁.Q.carrier
  /-- Open immersion into the second chart. -/
  f₂ : W ⟶ D₂.Q.carrier
  /-- The first map is an open immersion. -/
  f₁_open : IsOpenImmersion f₁
  /-- The second map is an open immersion. -/
  f₂_open : IsOpenImmersion f₂
  /-- The chart maps to the base agree on the overlap. -/
  chartMap_comm : f₁ ≫ D₁.chartMap = f₂ ≫ D₂.chartMap

namespace AffineChartOverlapWitness

variable {D₁ D₂ : AffineChartLocalQuotient S}
variable (W : AffineChartOverlapWitness D₁ D₂)

/-- The witness gives the expected overlap compatibility existential. -/
theorem toExists :
    ∃ (W : Scheme.{u}) (f₁ : W ⟶ D₁.Q.carrier) (f₂ : W ⟶ D₂.Q.carrier),
      IsOpenImmersion f₁ ∧ IsOpenImmersion f₂ ∧
        f₁ ≫ D₁.chartMap = f₂ ≫ D₂.chartMap :=
  ⟨W.W, W.f₁, W.f₂, W.f₁_open, W.f₂_open, W.chartMap_comm⟩

end AffineChartOverlapWitness

/-- The diagonal overlap witness: a local quotient chart overlaps itself on its
own carrier. -/
noncomputable def affineChartOverlapWitnessDiag
    (D : AffineChartLocalQuotient S) :
    AffineChartOverlapWitness D D where
  W := D.Q.carrier
  f₁ := 𝟙 _
  f₂ := 𝟙 _
  f₁_open := inferInstance
  f₂_open := inferInstance
  chartMap_comm := rfl

/-- Diagonal overlap compatibility, proved from the actual diagonal witness. -/
theorem affineChartOverlapCompatibility_diag
    (D : AffineChartLocalQuotient S) :
    ∃ (W : Scheme.{u}) (f₁ f₂ : W ⟶ D.Q.carrier),
      IsOpenImmersion f₁ ∧ IsOpenImmersion f₂ ∧
        f₁ ≫ D.chartMap = f₂ ≫ D.chartMap :=
  (affineChartOverlapWitnessDiag D).toExists

/-- Exact nontrivial-overlap obligation: every pair of local quotient charts
has an actual overlap witness.  This is a Prop; no inhabitant is asserted. -/
def AffineChartOverlapLocalizationCompatibility (S : Scheme.{u}) : Prop :=
  ∀ D₁ D₂ : AffineChartLocalQuotient S, Nonempty (AffineChartOverlapWitness D₁ D₂)

/-- The exact overlap obligation implies the overlap compatibility Prop of the
previous file, conditionally. -/
theorem affineChartQuotientOverlapCompatibility_of_localization
    (h : AffineChartOverlapLocalizationCompatibility S) :
    AffineChartQuotientOverlapCompatibility S :=
  by
    intro D₁ D₂
    rcases h D₁ D₂ with ⟨W⟩
    exact W.toExists

/-- The diagonal part is unconditional. -/
theorem affineChartOverlapLocalizationCompatibility_diag
    (D : AffineChartLocalQuotient S) :
    Nonempty (AffineChartOverlapWitness D D) :=
  ⟨affineChartOverlapWitnessDiag D⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapCompatProof
end