import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0NativeTensorConsumerActual
import tmp.sheaf.xif.paper.Mzk1P2DetCoefficientActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

/-! # P2: native tensor block alignment

The native tensor consumer is instantiated on the actual qVFamily tensor data:
K = T.arithmetic.F, p = qVFamTensorP, the one-factor index Unit, places
qVFamTensorPlaces and tuple qVFamTensorTuple.  Its block is definitionally
qVFamTensorBlock and its log-volume is the native theta readout.

Exact GAP: the native tensor block is not the product carrier
RootExtensionProductCarrier.  The latter is a coefficient readout (product of
local root extensions), while the native block is the tensor of base
completions; there is no canonical isometry/log-volume equality between them.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2NativeBlockAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeTensorConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetCoefficientActual
open MeasureTheory
open scoped BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The native tensor block at the actual qVFamily tensor data of b. -/
abbrev p2NativeBlock (b : Bad (nativePlaceSelection T)) : Type :=
  NativeTensorBlock (p := qVFamTensorP T b) (qVFamTensorPlaces T b) qVFamTensorTuple

/-- The native block is definitionally the actual qVFamily tensor block. -/
theorem p2NativeBlock_eq_qVFamTensorBlock (b : Bad (nativePlaceSelection T)) :
    p2NativeBlock (T := T) b = qVFamTensorBlock T b := rfl

/-- The native tensor log-volume at the qVFamily data is the native theta readout. -/
theorem p2NativeBlock_logVolume_eq_nativeThetaReadout
    (b : Bad (nativePlaceSelection T)) :
    nativeTensorLogVolume (p := qVFamTensorP T b)
        (qVFamTensorPlaces T b) qVFamTensorTuple =
      nativeThetaReadout T b := rfl

/-- Actual native tensor packet at the qVFamily tensor data. -/
noncomputable def p2NativeBlockPacket (b : Bad (nativePlaceSelection T)) :
    NativeTensorPacket (p := qVFamTensorP T b)
      (qVFamTensorPlaces T b) qVFamTensorTuple :=
  nativeTensorPacket (p := qVFamTensorP T b)
    (qVFamTensorPlaces T b) qVFamTensorTuple

/-- The packet's log-volume is the native theta readout. -/
theorem p2NativeBlockPacket_logVolume
    (b : Bad (nativePlaceSelection T)) :
    (p2NativeBlockPacket T b).logVolume = nativeThetaReadout T b := rfl

/-- Exact missing alignment between the native tensor block and the product
carrier of root extensions. -/
def p2NativeProductBlockMissing : List String :=
  [ "native tensor block over base completions <-> product of root extensions L_b",
    "no canonical isometry between finite p-adic tensor and Pi product carrier",
    "log-volume transport would require an explicit isometry, not just a linear equivalence" ]

theorem p2NativeProductBlockMissing_length :
    p2NativeProductBlockMissing.length = 3 := rfl

#check p2NativeBlock
#check p2NativeBlock_eq_qVFamTensorBlock
#check p2NativeBlock_logVolume_eq_nativeThetaReadout
#check p2NativeBlockPacket
#check p2NativeBlockPacket_logVolume
#check p2NativeProductBlockMissing
end LeanFormal.IUT.XiFPaper.Mzk1P2NativeBlockAlignmentActual
end
