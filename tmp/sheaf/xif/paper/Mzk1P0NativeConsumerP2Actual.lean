import tmp.sheaf.xif.paper.Mzk1P0NativeTensorConsumerActual
import tmp.sheaf.xif.paper.Mzk1P2DetCoefficientActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import Mathlib.Tactic

/-! # P0 native tensor consumer with P2 coefficient data

The native tensor packet is built from p/places/tuple only.  The P2 coefficient
data is the actual root pure-tensor family.  They are combined as an actual
pair of packets; no place alignment between the native number field K and the
root-extension bad set is assumed.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeConsumerP2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeTensorConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {K : Type} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι]
variable {V : ι -> Type} [∀ i, Fintype (V i)]

/-- Combined native tensor packet and P2 pure-tensor coefficient data. -/
structure NativeP2ConsumerData
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) where
  tensor : NativeTensorPacket (p := p) places tuple
  coeff : RootExtensionProductCarrier T
  coeff_mem : coeff ∈ rootExtensionProductUnitBall T
  coeff_det_pos : 0 < detCoefficientNorm T coeff
  correctedLogVolume : Real
  correctedLogVolume_eq : correctedLogVolume =
    tensor.logVolume - Real.log (detCoefficientNorm T coeff)

/-- Actual combined consumer from an actual native tensor packet and actual
P2 coefficients. -/
noncomputable def nativeP2Consumer
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i)
    (coeff : RootExtensionProductCarrier T)
    (hcoeff : coeff ∈ rootExtensionProductUnitBall T)
    (hpos : 0 < detCoefficientNorm T coeff) :
    NativeP2ConsumerData (p := p) (T := T) places tuple where
  tensor := nativeTensorPacket (p := p) places tuple
  coeff := coeff
  coeff_mem := hcoeff
  coeff_det_pos := hpos
  correctedLogVolume :=
    (nativeTensorPacket (p := p) places tuple).logVolume -
      Real.log (detCoefficientNorm T coeff)
  correctedLogVolume_eq := rfl

theorem nativeP2Consumer_tensorLogVolume
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i)
    (coeff : RootExtensionProductCarrier T)
    (hcoeff : coeff ∈ rootExtensionProductUnitBall T)
    (hpos : 0 < detCoefficientNorm T coeff) :
    (nativeP2Consumer (T := T) (p := p) places tuple coeff hcoeff hpos).tensor.logVolume =
      (nativeTensorPacket (p := p) places tuple).logVolume := rfl

/-- Exact alignment gap: the native number-field places and the bad indices of T
have no canonical identification in the current tree. -/
def nativeP2AlignmentMissing : List String :=
  [ "FinitePlaceAtPrime K p <-> Bad (nativePlaceSelection T) place alignment",
    "native tensor block <-> RootExtensionProductCarrier T block equivalence",
    "common archimedean determinant metric on the combined carrier" ]

theorem nativeP2AlignmentMissing_length : nativeP2AlignmentMissing.length = 3 := rfl

#check NativeP2ConsumerData
#check nativeP2Consumer
#check nativeP2Consumer_tensorLogVolume
#check nativeP2AlignmentMissing
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeConsumerP2Actual
end
