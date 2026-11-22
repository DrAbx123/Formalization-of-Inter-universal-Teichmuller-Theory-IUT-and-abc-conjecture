import tmp.sheaf.xif.paper.ThetaPilotHullNormalizationActual
import LeanFormal.IUT.Foundations.Arithmetic.FiniteLabels

/-! # ThetaPilotCarrier / F_l^x index data and obstruction

The project ThetaPilotCarrier is Fin (lStar l.value + 1), the stages 0,...,l*.
The paper's procession labels are F_l^x = (ZMod l)^x.  This file constructs the
actual reverse map from ThetaPilotCarrier stages into F_l^x using the actual
unit 2 (2 is nonzero for prime l >= 5), and proves the exact obstruction to an
injective F_l^x -> ThetaPilotCarrier index map from cardinalities.

The reverse map n |-> 2^n is an actual function but is not the paper's source
action/index data.  The exact required source object is an actual F_l^x action
on the Theta-pilot processions compatible with the Kummer/procession
normalization; no arbitrary equivalence is asserted.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ThetaPilotCarrierFIndexActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual unit 2 in F_l^x for prime l >= 5. -/
def stageBaseUnit : FlUnits (l := l) :=
  Units.mk0 (2 : ZMod l.value) (two_ne_zero_Fl l.value l.ge_five)

/-- Actual reverse map: ThetaPilotCarrier stage n maps to 2^n in F_l^x. -/
def thetaPilotStageToFlUnits (n : ThetaPilotCarrier l) : FlUnits (l := l) :=
  stageBaseUnit (l := l) ^ (n : Nat)

@[simp] theorem thetaPilotStageToFlUnits_zero :
    thetaPilotStageToFlUnits (l := l) ⟨0, Nat.succ_pos _⟩ = 1 := by
  unfold thetaPilotStageToFlUnits
  simp

/-- Exact index obstruction: there is no injective map from F_l^x into the
ThetaPilotCarrier stages, because the cardinalities are ordered oppositely. -/
theorem not_exists_injective_flUnits_to_thetaPilotCarrier :
    ¬ ∃ f : FlUnits (l := l) -> ThetaPilotCarrier l,
      Function.Injective f := by
  rintro ⟨f, hf⟩
  have hle : Fintype.card (FlUnits (l := l)) <=
      Fintype.card (ThetaPilotCarrier l) :=
    Fintype.card_le_of_injective f hf
  rw [flUnits_card, thetaPilotCarrier_card] at hle
  have hl5 : 5 <= l.value := l.ge_five
  have hodd : Odd l.value :=
    (Fact.out : Nat.Prime l.value).odd_of_ne_two (by omega)
  have hstar := two_mul_lStar_add_one l.value hodd
  omega

/-- Exact obstruction proposition. -/
def ThetaPilotFlIndexObstruction : Prop :=
  ¬ ∃ f : FlUnits (l := l) -> ThetaPilotCarrier l,
    Function.Injective f

theorem thetaPilotFlIndexObstruction_holds :
    ThetaPilotFlIndexObstruction (l := l) :=
  not_exists_injective_flUnits_to_thetaPilotCarrier

/-- Required actual source object: an index/action map from the paper's F_l^x
into the Theta-pilot processions, injective and compatible with the Kummer/
procession action.  The cardinal obstruction above shows that the project
ThetaPilotCarrier cannot be that target without a larger actual carrier. -/
structure ThetaPilotFlIndexSourceData where
  indexMap : FlUnits (l := l) -> ThetaPilotCarrier l
  indexMap_injective : Function.Injective indexMap
  action_compat : Prop

theorem no_thetaPilotFlIndexSourceData :
    ¬ Nonempty (ThetaPilotFlIndexSourceData (l := l)) := by
  rintro ⟨S⟩
  exact not_exists_injective_flUnits_to_thetaPilotCarrier
    ⟨S.indexMap, S.indexMap_injective⟩

end LeanFormal.IUT.XiFPaper.ThetaPilotCarrierFIndexActual

end
