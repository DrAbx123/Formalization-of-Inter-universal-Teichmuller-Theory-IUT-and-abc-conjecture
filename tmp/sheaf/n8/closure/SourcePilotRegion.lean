import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.IUTII.Kummer.KummerClass

/-!
# C3 stage 2 — SourcePilotRegionData (finite-place actual q/theta schema)

The C1 and C2 stage-2 files exist as tmp sources but their oleans are not
available to this file. This file therefore exposes the C3 schema with exact
C1/C2 parameter-interface obligations in the docstring of
sourcePilotRegion_nonempty, and does NOT copy the C2 type.

C3-STAGE1 section 3.2 fields represented here with actual types:
- q_v : FinitePlaceQCandidate place, i.e. an element of the actual completion,
  not a Real scalar;
- thetaPacket : FiniteThetaPacket l;
- Kummer class/root: NatRootSystem / CyclotomicTower and
  KummerClass.rootSystemDiff, tied to the actual q unit;
- integer lattice/tensor landing: ArithmeticTensorTupleBlock with actual
  finite-place data and a landing map tied to q by an equation;
- root-change: an actual CyclotomicTower with a definitional
  equation to rootSystemDiff.

No unconditional inhabitant is constructed; the unused named-sorry theorem
sourcePilotRegion_nonempty has been removed. Exact
gaps: q source Real/Completion identification, theta-pilot point without a
free SourceImageRealization (A1), actual Kummer class from a source action, a
source-constructed tensor landing, root-change compatibility with source roots,
and C1/C2 actual data. No production file is modified.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui u v w

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped Pointwise

variable {l : PrimeGeFive} {V : Type uv}

/-- Actual q-pilot unit in the completion, built from a nonzero q-parameter. -/
def candidateUnits
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime K p) (q : FinitePlaceQCandidate place.val) :
    (CommonPrimeCompletion (K := K) place)ˣ :=
  Units.mk0 q.q q.q_ne_zero

/-- C3 stage-2 data for one actual finite place. C1 and C2 are external
parameter interfaces (see the module docstring); their actual values are not
imported or copied here. -/
structure SourcePilotRegionData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- Residue prime of the selected finite place. -/
  p : Nat
  /-- The actual finite place. -/
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  /-- Actual q in the completion field, not a Real scalar. -/
  q : FinitePlaceQCandidate place.val
  /-- The actual finite theta packet from the source theta special values. -/
  thetaPacket : FiniteThetaPacket l
  /-- q as an actual unit of the completion. -/
  qUnit : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ
  /-- The q unit is the actual q element. -/
  qUnit_eq : qUnit = candidateUnits (K := I.initial.arithmetic.Fmod) place q
  /-- Actual Kummer root system for the q unit. -/
  roots : NatRootSystem qUnit
  /-- A second root system used to represent root change. -/
  roots' : NatRootSystem qUnit
  /-- Actual Kummer class tower. -/
  kummerClass : CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
  /-- Actual root-change tower. -/
  rootChange : CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
  /-- Root change is the Kummer root-system difference. -/
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
  /-- Finite index of the arithmetic tensor factors. -/
  tensorIndex : Type v
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex → Type w
  tensorPlaces : (i : tensorIndex) → tensorPlaceIndex i →
    FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  tensorTuple : (i : tensorIndex) → tensorPlaceIndex i
  /-- Actual integer-lattice/tensor unit. -/
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  /-- Actual landing map from the completion to the tensor block. -/
  tensorLanding : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place →
    ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  /-- The q element lands at the tensor unit. -/
  tensorLanding_q : tensorLanding (q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

attribute [instance] SourcePilotRegionData.hp
attribute [instance] SourcePilotRegionData.tensorFintype

end LeanFormal.IUT.N8Closure.SourcePilotRegion
