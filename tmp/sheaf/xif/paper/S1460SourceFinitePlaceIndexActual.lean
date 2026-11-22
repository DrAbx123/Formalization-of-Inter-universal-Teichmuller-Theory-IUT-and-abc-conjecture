import tmp.sheaf.xif.paper.S1427Ind3PlaceComparisonActual
import tmp.sheaf.xif.paper.S1321PaperOriginalInputActual

/-! # S1460: actual source finite-place index and Ind3 carrier

S1427 reduced the integral Ind3 place comparison to

```text
SourceFinitePlaceIndex I = V -> NumberField.FinitePlace I.initial.arithmetic.Fmod
```

This file supplies the actual index when the source place type `V` is a
concrete finite-place index type, i.e. when an actual equivalence

```text
e : V ≃ NumberField.FinitePlace I.initial.arithmetic.Fmod
```

is present.  The identity case `V = FinitePlace Fmod` is the canonical
concrete index; no `Classical.choice`, no constant map and no arbitrary place
selection is used.  From the index the actual comparison and the actual
integral Ind3 carrier are constructed via S1427.

For the current S1280 `PaperOriginalInput` the place type is `Unit`, not a
finite-place index type; there is no actual `Unit ≃ FinitePlace Fmod`, so the
concrete Gaussian input cannot use this construction without an arbitrary
constant place map (which is forbidden).  The exact first field for that input
is therefore a concrete finite-place index type with its actual equivalence,
not `Unit`.

Everything below is conditional on the actual equivalence `e`; the equivalence
is the source datum, not fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1460SourceFinitePlaceIndexActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1427Ind3PlaceComparisonActual
open LeanFormal.IUT.XiFPaper.S1327Ind3IntegralLogShellActual
open LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (e : V ≃ NumberField.FinitePlace I.initial.arithmetic.Fmod)

/-- The actual source finite-place index map induced by the actual equivalence
between the source place type and the finite places of the modified field. -/
noncomputable def sourceFinitePlaceIndexOfEquiv
    (e : V ≃ NumberField.FinitePlace I.initial.arithmetic.Fmod) :
    SourceFinitePlaceIndex I :=
  e

/-- Pointwise value of the actual source finite-place index. -/
@[simp] theorem sourceFinitePlaceIndexOfEquiv_apply (v : V) :
    sourceFinitePlaceIndexOfEquiv I e v = e v := rfl

/-- Nonemptiness of the actual source finite-place index. -/
theorem sourceFinitePlaceIndexOfEquiv_nonempty
    (e : V ≃ NumberField.FinitePlace I.initial.arithmetic.Fmod) :
    Nonempty (SourceFinitePlaceIndex I) := ⟨sourceFinitePlaceIndexOfEquiv I e⟩

/-- The actual integral Ind3 place comparison obtained from the index. -/
noncomputable def actualIntegralInd3PlaceComparison
    (e : V ≃ NumberField.FinitePlace I.initial.arithmetic.Fmod) :
    IntegralInd3PlaceComparison I :=
  comparisonOfFinitePlaceIndex I (sourceFinitePlaceIndexOfEquiv I e)

/-- Its first component is the rational prime under the indexed finite place. -/
@[simp] theorem actualIntegralInd3PlaceComparison_fst (v : V) :
    (actualIntegralInd3PlaceComparison I e v).1 =
      completionRationalPrime (e v) := rfl

/-- Its actual finite place is the indexed finite place. -/
@[simp] theorem actualIntegralInd3PlaceComparison_snd_val (v : V) :
    ((actualIntegralInd3PlaceComparison I e v).2).val = e v := rfl

/-- The corresponding actual integral Ind3 carrier at capsule level `j`. -/
noncomputable def actualInd3Carrier
    (e : V ≃ NumberField.FinitePlace I.initial.arithmetic.Fmod) (j : Nat) :
    Ind3LogShellCarrier.{uv, 0, ua} (V := V) (R := ℤ) j :=
  carrierOfSourceFinitePlaceIndex I j (sourceFinitePlaceIndexOfEquiv I e)

/-- Its first field is the actual integral log-shell at the indexed place. -/
@[simp] theorem actualInd3Carrier_shell (j : Nat) (i : Capsule j) (v : V) :
    (actualInd3Carrier I e j).shell i v =
      integralShell I (completionRationalPrime (e v)) ⟨e v, rfl⟩ :=
  carrierOfSourceFinitePlaceIndex_shell I j (sourceFinitePlaceIndexOfEquiv I e) i v

/-- The actual Ind3 stage datum at level `j` and integer `n`. -/
noncomputable def actualInd3StageDatum
    (e : V ≃ NumberField.FinitePlace I.initial.arithmetic.Fmod)
    (n : Int) (j : Nat) :
    IntegralInd3StageDatumAtV I (actualIntegralInd3PlaceComparison I e) n j :=
  integralInd3StageDatumAtV I (actualIntegralInd3PlaceComparison I e) n j

end LeanFormal.IUT.XiFPaper.S1460SourceFinitePlaceIndexActual
end
