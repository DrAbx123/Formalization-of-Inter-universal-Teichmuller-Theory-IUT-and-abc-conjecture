import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Source arithmetic place data for the tensor-block parameters

This file connects the source input `OriginalInput` to the parameters required
by the existing arithmetic tensor block.  It deliberately does not construct
Tate uniformization, a theta-pilot unit lift, or an N5 comparison.

## Handoff status (2026-10-18)

- File: `D:\lean\LeanFormal\IUT\IUTIII\Theorem311\SourceArithmeticPlaceModel.lean`.
- Last build: `D:\lean\tmp\n4n7-consolidation-20261017\source-place-model-build2.log`;
  guard exit `0`, `3779` jobs, `88.5s`.
- Declarations covered by `#print axioms`: `SourceArithmeticPlaceModel`,
  `SourceArithmeticTensorData`, `SourceArithmeticTensorData.block_nonempty`,
  `SourceArithmeticTensorData.qParameter_exponent_pos`, and
  `SourceArithmeticTensorData.pilotWeight_pos`; all report
  `[propext, Classical.choice, Quot.sound]`.
- Boundary: `qParameter` is an input `FinitePlaceQCandidate`, not a construction
  of an elliptic-curve Tate parameter and not a proof of B1/B7/B8.  The file
  also does not assert an equality between the opaque source `selectedPlaces`
  type and `FinitePlaceAtPrime`; that missing bridge is recorded above.
- Next alignment task: construct the source/arithmetic comparison from the
  actual Tate q data (B1/B7/B8) to `FinitePlaceQCandidate`, including the
  `ord(q)`/`thetaPacket.q`/scale compatibility needed for the pilot region.
- Recon correction: `n5-source-recon-20261018.md` §10.10 was appended
  successfully at line 620, retaining the older text.
-/

namespace LeanFormal.IUT
namespace Theorem311Source

open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui vι wW

/-- The finite-place parameters used by `ArithmeticTensorTupleBlock`.

`places` and `tuple` are supplied data.  The field `selection` records a source
index for each tensor factor, but no equality between `places` and
`I.initial.selectedPlaces` is asserted: in the current source boundary,
`selectedPlaces` and `badPlaces` are opaque `Type u` fields
(`SourceDefinition31Boundary.lean:660-664`), not subtypes of
`NumberField.FinitePlace`.  The bridge from the source-selected place type to
`FinitePlaceAtPrime` is therefore a genuine missing definition and is not
fabricated here. -/
structure SourceArithmeticPlaceModel (l : PrimeGeFive) (V : Type uv)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  p : ℕ
  [factPrime : Fact p.Prime]
  ι : Type vι
  [fintypeι : Fintype ι]
  W : ι → Type wW
  [fintypeW : ∀ i, Fintype (W i)]
  places : (i : ι) → W i → FinitePlaceAtPrime I.initial.arithmetic.K p
  tuple : (i : ι) → W i
  selection : ι → I.initial.selectedPlaces

attribute [instance] SourceArithmeticPlaceModel.factPrime
  SourceArithmeticPlaceModel.fintypeι
  SourceArithmeticPlaceModel.fintypeW

/-- Input q-candidates attached to the selected finite places.

This records only the valuation-theoretic `FinitePlaceQCandidate` data.  It is
not a construction of a Tate parameter for the source elliptic curve, and it is
not the assertion that the elliptic curve is uniformized by a multiplicative
quotient.  The header of `LocalQParameter.lean` (lines 5-16) states that
Mathlib does not currently supply the Tate uniformization theorem. -/
structure SourceArithmeticTensorData
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (M : SourceArithmeticPlaceModel l V I) where
  qParameter : (i : M.ι) →
    FinitePlaceQCandidate (M.places i (M.tuple i)).val

namespace SourceArithmeticTensorData

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {M : SourceArithmeticPlaceModel l V I}

/-- The tuple tensor block determined by the model parameters. -/
abbrev block (D : SourceArithmeticTensorData (I := I) M) : Type _ :=
  ArithmeticTensorTupleBlock M.places M.tuple

/-- The tensor block is inhabited by zero. -/
theorem block_nonempty (D : SourceArithmeticTensorData (I := I) M) :
    Nonempty (block D) :=
  ⟨0⟩

/-- Every input q-candidate has positive local exponent (order). -/
theorem qParameter_exponent_pos
    (D : SourceArithmeticTensorData (I := I) M) (i : M.ι) :
    0 < (D.qParameter i).exponent :=
  (D.qParameter i).exponent_pos

/-- For `j ≥ 1`, the theta-pilot weight `j^2` and the product with the local
q-exponent are positive. -/
theorem pilotWeight_pos
    (D : SourceArithmeticTensorData (I := I) M)
    (j : ℕ) (hj : 1 ≤ j) (i : M.ι) :
    0 < j ^ 2 ∧
      0 < (j ^ 2 : Int) * (D.qParameter i).exponent := by
  have hjpos : 0 < j := lt_of_lt_of_le Nat.zero_lt_one hj
  constructor
  · exact pow_pos hjpos 2
  · have hsq : 0 < (j ^ 2 : Int) := by
      exact_mod_cast (pow_pos hjpos 2)
    exact mul_pos hsq (D.qParameter i).exponent_pos

end SourceArithmeticTensorData

#print axioms LeanFormal.IUT.Theorem311Source.SourceArithmeticPlaceModel
#print axioms LeanFormal.IUT.Theorem311Source.SourceArithmeticTensorData
#print axioms LeanFormal.IUT.Theorem311Source.SourceArithmeticTensorData.block_nonempty
#print axioms LeanFormal.IUT.Theorem311Source.SourceArithmeticTensorData.qParameter_exponent_pos
#print axioms LeanFormal.IUT.Theorem311Source.SourceArithmeticTensorData.pilotWeight_pos

end Theorem311Source
end LeanFormal.IUT
