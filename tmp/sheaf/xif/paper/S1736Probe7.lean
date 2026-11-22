import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1736Probe7
open CategoryTheory
open CategoryTheory.Limits
universe u v

structure GaloisFields (C : Type u) [Category.{v} C] : Prop where
  finiteLimits : HasFiniteLimits C
  finiteCoproducts : HasFiniteCoproducts C
  finiteGroupQuotients : (G : Type v) → [Group G] → [Finite G] →
    HasColimitsOfShape (SingleObj G) C
  monoDirectSummand : ∀ {X Y : C} (i : X ⟶ Y) [Mono i],
    ∃ (Z : C) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))

theorem preGaloisCategory_iff_fields (C : Type u) [Category.{v} C] :
    PreGaloisCategory C ↔ GaloisFields C := by
  constructor
  · intro h
    haveI : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
    exact
      { finiteLimits := inferInstance
        finiteCoproducts := h.hasFiniteCoproducts
        finiteGroupQuotients := fun G _ _ => h.hasQuotientsByFiniteGroups G
        monoDirectSummand := fun i _ => h.monoInducesIsoOnDirectSummand i }
  · intro h
    haveI : HasFiniteLimits C := h.finiteLimits
    exact
      { hasTerminal := inferInstance
        hasPullbacks := inferInstance
        hasFiniteCoproducts := h.finiteCoproducts
        hasQuotientsByFiniteGroups := fun G _ _ => h.finiteGroupQuotients G
        monoInducesIsoOnDirectSummand := fun i _ => h.monoDirectSummand i }

end LeanFormal.IUT.XiFPaper.S1736Probe7
