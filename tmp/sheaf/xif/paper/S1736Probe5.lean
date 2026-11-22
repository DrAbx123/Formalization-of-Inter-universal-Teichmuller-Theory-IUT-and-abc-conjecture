import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1736Probe5
open CategoryTheory
open CategoryTheory.Limits
universe u v

structure PreGaloisFields (C : Type u) [Category.{v} C] : Prop where
  terminal : HasTerminal C
  pullbacks : HasPullbacks C
  finiteCoproducts : HasFiniteCoproducts C
  finiteGroupQuotients : (G : Type v) → [Group G] → [Finite G] →
    HasColimitsOfShape (SingleObj G) C
  monoDirectSummand : ∀ {X Y : C} (i : X ⟶ Y) [Mono i],
    ∃ (Z : C) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))

theorem preGaloisCategory_iff_fields (C : Type u) [Category.{v} C] :
    PreGaloisCategory C ↔ PreGaloisFields C := by
  constructor
  · intro h
    exact
      { terminal := h.hasTerminal
        pullbacks := h.hasPullbacks
        finiteCoproducts := h.hasFiniteCoproducts
        finiteGroupQuotients := fun G _ _ => h.hasQuotientsByFiniteGroups G
        monoDirectSummand := fun i _ => h.monoInducesIsoOnDirectSummand i }
  · intro h
    exact
      { hasTerminal := h.terminal
        hasPullbacks := h.pullbacks
        hasFiniteCoproducts := h.finiteCoproducts
        hasQuotientsByFiniteGroups := fun G _ _ => h.finiteGroupQuotients G
        monoInducesIsoOnDirectSummand := fun i _ => h.monoDirectSummand i }

end LeanFormal.IUT.XiFPaper.S1736Probe5
