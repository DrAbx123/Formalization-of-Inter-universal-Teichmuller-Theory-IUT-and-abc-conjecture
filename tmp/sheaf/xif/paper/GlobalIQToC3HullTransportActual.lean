import tmp.sheaf.xif.paper.C3TensorPlaceLiteralIQIndexActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks

/-!
# Global IQ -> C3 hull transport: actual index alignment and the value-level gap

The actual C3/LiteralIQ index comparison identifies the place families, and the
actual C3 tensor packet has an actual projection to the C3 log-shell tensor
block.  However, the global IQ ambient has the extra tensor factor
`Fin (j+1)` and the completion-packet places, while the C3 hull block is the
selected-tuple tensor block.  There is no actual value-level transport that
collapses the extra global tensor factor into the C3 block.

This file constructs:

* the actual C3/LiteralIQ index comparison;
* the actual single-factor C3 packet -> C3 hull block projection;
* the exact object-level gap for the global IQ ambient -> C3 hull transport.

No fake carrier comparison or image inclusion is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper
namespace GlobalIQToC3HullTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3TensorPlaceLiteralIQIndexActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
open LeanFormal.IUT.ABCBridge.Geometry

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- The actual C3/LiteralIQ index and place comparison at level j. -/
abbrev ActualC3LiteralIQIndexComparison (j : Nat) :=
  C3TensorPlaceLiteralIQComparison (I := I) (C3 := C3) j

/-- The actual comparison at every procession level. -/
noncomputable def actualC3LiteralIQIndexComparison (j : Nat) :
    ActualC3LiteralIQIndexComparison (I := I) (C3 := C3) j :=
  c3TensorPlaceLiteralIQComparison (I := I) (C3 := C3) j

/-- The actual single-factor C3 tensor packet over the C3 tensor places. -/
abbrev C3SinglePacket : Type :=
  ArithmeticPacketTensor C3.tensorPlaces

/-- The actual C3 log-shell tensor block. -/
abbrev C3HullBlock : Type :=
  C3LogShellTensorBlock C3

/-- The actual projection from the single-factor C3 packet to the selected C3
log-shell tensor block. -/
noncomputable def c3SinglePacketToHullBlock :
    C3SinglePacket (C3 := C3) →ₗ[ℚ_[C3.p]] C3HullBlock (C3 := C3) :=
  arithmeticTensorTupleProjection C3.tensorPlaces C3.tensorTuple

/-- The actual projection sends the actual tensor log region to the actual C3
tensor-log region. -/
theorem c3SinglePacketToHullBlock_image_region :
    c3SinglePacketToHullBlock (C3 := C3) '' arithmeticTensorLogRegion C3.tensorPlaces =
      actualC3LogShellTensorRegion (C3 := C3) := by
  exact arithmeticTensorTupleProjection_image_logRegion
    C3.tensorPlaces C3.tensorTuple

/-- The actual global IQ ambient at level j. -/
abbrev GlobalIQAmbient (j : Nat) : Type :=
  LiteralIQAmbient (C3 := C3) j

/-- Exact object-level gap: the global IQ ambient has the extra tensor factor
and packet places; no actual value-level map to the C3 hull block is supplied. -/
structure GlobalIQToC3TransportGap (j : Nat) : Prop where
  indexAlignment : Prop
  extraFactorCollapse : Prop
  valueLevelTransport : Prop
  imageToHullMap : Prop
  imageLandsInHull : Prop
  regionTransport : Prop

/-- The exact missing transport object. -/
def GlobalIQToC3TransportRequired (j : Nat) : Prop :=
  Nonempty (GlobalIQToC3TransportGap (I := I) (C3 := C3) j)

/-- Actual data: the index comparison, the single-factor projection, and the
single-factor region image equality.  The global transport remains the exact
gap above. -/
structure GlobalIQToC3TransportActualData (j : Nat) where
  comparison : ActualC3LiteralIQIndexComparison (I := I) (C3 := C3) j
  comparison_eq : comparison =
    actualC3LiteralIQIndexComparison (I := I) (C3 := C3) j
  singlePacketMap : C3SinglePacket (C3 := C3) →ₗ[ℚ_[C3.p]] C3HullBlock (C3 := C3)
  singlePacketMap_eq : singlePacketMap =
    c3SinglePacketToHullBlock (C3 := C3)
  singlePacketRegionImage_eq :
    singlePacketMap '' arithmeticTensorLogRegion C3.tensorPlaces =
      actualC3LogShellTensorRegion (C3 := C3)
  globalIQCarrier : Type
  globalIQCarrier_eq : globalIQCarrier = GlobalIQAmbient (C3 := C3) j
  globalToHullGap : Prop
  globalToHullGap_eq : globalToHullGap =
    GlobalIQToC3TransportRequired (I := I) (C3 := C3) j

/-- The actual index/projection data with the global transport gap. -/
noncomputable def globalIQToC3TransportActualData (j : Nat) :
    GlobalIQToC3TransportActualData (I := I) (C3 := C3) j where
  comparison := actualC3LiteralIQIndexComparison (I := I) (C3 := C3) j
  comparison_eq := rfl
  singlePacketMap := c3SinglePacketToHullBlock (C3 := C3)
  singlePacketMap_eq := rfl
  singlePacketRegionImage_eq :=
    c3SinglePacketToHullBlock_image_region (C3 := C3)
  globalIQCarrier := GlobalIQAmbient (C3 := C3) j
  globalIQCarrier_eq := rfl
  globalToHullGap := GlobalIQToC3TransportRequired (I := I) (C3 := C3) j
  globalToHullGap_eq := rfl


/-- At level 0 the extra tensor index is `Fin 1`; the actual index equivalence
collapses it to the C3 tensor index. -/
def literalIQIndexZeroEquiv :
    LiteralIQIndex (C3 := C3) 0 ≃ C3.tensorIndex where
  toFun x := x.2
  invFun i := (⟨0, Nat.succ_pos 0⟩, i)
  left_inv x := by
    obtain ⟨t, i⟩ := x
    congr 1
    exact Subsingleton.elim t _
  right_inv i := rfl

/-- The actual selected tuple for the level-0 literal IQ tensor factors. -/
def levelZeroTuple :
    (x : LiteralIQIndex (C3 := C3) 0) -> C3.tensorPlaceIndex x.2 :=
  fun x => C3.tensorTuple x.2

/-- The actual level-0 transport from the global IQ ambient to the C3
log-shell tensor block: project each completion packet to the selected tuple,
then reindex the literal IQ factor to the C3 tensor index. -/
noncomputable def globalIQToC3HullLevelZero :
    GlobalIQAmbient (C3 := C3) 0 →ₗ[ℚ_[C3.p]] C3HullBlock (C3 := C3) :=
  let tuple : (x : LiteralIQIndex (C3 := C3) 0) -> C3.tensorPlaceIndex x.2 :=
    levelZeroTuple (C3 := C3)
  let s : LiteralIQIndex (C3 := C3) 0 -> Type :=
    fun x => CommonPrimeCompletion
      (literalIQPlaces (C3 := C3) 0 x (tuple x))
  (PiTensorProduct.reindex (R := ℚ_[C3.p]) (s := s)
    (e := literalIQIndexZeroEquiv (C3 := C3))).toLinearMap.comp
    (arithmeticTensorTupleProjection
      (literalIQPlaces (C3 := C3) 0) tuple)

/-- Exact gap for the positive levels: the extra `Fin (j+1)` tensor factors
cannot be collapsed without a level choice and a normalization of the remaining
factors. -/
structure ExtraFactorCollapseGap (j : Nat) : Prop where
  extraTensorFactors : Prop
  levelChoice : Prop
  remainingFactorNormalization : Prop
  valueLevelTransport : Prop
  paperLevelSymmetry : Prop

/-- Exact missing extra-factor collapse object. -/
def ExtraFactorCollapseRequired (j : Nat) : Prop :=
  Nonempty (ExtraFactorCollapseGap (I := I) (C3 := C3) j)

end GlobalIQToC3HullTransportActual
end LeanFormal.IUT.XiFPaper
end
