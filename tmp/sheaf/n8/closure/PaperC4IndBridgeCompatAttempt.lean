import tmp.sheaf.n8.closure.PaperC4IndBridgeActualAttempt

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperC4IndBridgeCompatAttempt

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.C4IndActionPaperAttempt
open LeanFormal.IUT.N8Closure.PaperC4IndBridgeActualAttempt
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I
  (Multiplicative (finiteLabel l)))

/-! ## Specialized compatibility law -/

/-- Compatibility data for the specialized bridge: the label map is additive
and the actual C4 Ind1 action is multiplicative on translated labels. -/
structure PaperC4ActionCompatibility where
  labelMap_add : ∀ (t x : finiteLabel l),
    (actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap (t + x) =
      (actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap t *
        (actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap x
  c4Action_add : ∀ (t x : finiteLabel l),
    (actualPaperC4IndBridge (l := l) (V := V) I C4).c4Action
        ((actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap (t + x)) =
      (actualPaperC4IndBridge (l := l) (V := V) I C4).c4Action
          ((actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap t) *
        (actualPaperC4IndBridge (l := l) (V := V) I C4).c4Action
          ((actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap x)

theorem specialized_labelMap_add (t x : finiteLabel l) :
    (actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap (t + x) =
      (actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap t *
        (actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap x := by
  rfl

theorem specialized_c4Action_add (t x : finiteLabel l) :
    (actualPaperC4IndBridge (l := l) (V := V) I C4).c4Action
        ((actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap (t + x)) =
      (actualPaperC4IndBridge (l := l) (V := V) I C4).c4Action
          ((actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap t) *
        (actualPaperC4IndBridge (l := l) (V := V) I C4).c4Action
          ((actualPaperC4IndBridge (l := l) (V := V) I C4).labelMap x) := by
  simp [actualPaperC4IndBridge, map_mul]

theorem actualPaperC4ActionCompatibility :
    PaperC4ActionCompatibility (l := l) (V := V) I C4 where
  labelMap_add := specialized_labelMap_add (l := l) (V := V) I C4
  c4Action_add := specialized_c4Action_add (l := l) (V := V) I C4

theorem actualPaperC4ActionCompatibility_nonempty :
    Nonempty (PaperC4ActionCompatibility (l := l) (V := V) I C4) :=
  ⟨actualPaperC4ActionCompatibility (l := l) (V := V) I C4⟩

end LeanFormal.IUT.N8Closure.PaperC4IndBridgeCompatAttempt
