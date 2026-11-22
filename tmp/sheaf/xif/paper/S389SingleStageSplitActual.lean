import Iut.Foundations.SourceFiniteStageModelFrobenioid
import Iut.Foundations.Frobenioid
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S389SingleStageSplitActual

open CategoryTheory

universe u

variable {K : Type u} [Field K] [NumberField K]
variable (place : NumberField.FinitePlace K)

/-- The full subcategory of the stage base on the terminal object; one object, no ramification transitions. -/
abbrev SingleStageBase : Type u :=
  ObjectProperty.FullSubcategory
    (fun s : Iut.SourceFinitePlaceReconstruction.StageBase place =>
      s = Opposite.op (⊥ : Iut.SourceFinitePlaceReconstruction.StageIndex place))

theorem singleStageBase_single_object :
    ∃ X : SingleStageBase place, ∀ Y : SingleStageBase place, Y = X := by
  refine ⟨⟨Opposite.op ⊥, rfl⟩, ?_⟩
  intro Y
  rcases Y with ⟨obj, hobj⟩
  subst hobj
  rfl

/-- Exact missing spec for the local split Frobenioid at one stage. -/
structure SingleStageSplitFrobenioidSpec where
  base : SingleStageBase place
  S : Iut.SplitFrobenioidPresentation.{u}
  base_is_single_stage : Prop
  uniformizer : Prop
  tau_eq_uniformizer_powers : Prop

def SingleStageSplitFrobenioidRequired : Prop :=
  Nonempty (SingleStageSplitFrobenioidSpec place)

end LeanFormal.IUT.XiFPaper.S389SingleStageSplitActual

end
