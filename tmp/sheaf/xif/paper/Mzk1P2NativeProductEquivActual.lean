import tmp.sheaf.xif.paper.Mzk1P2NativeBlockAlignmentActual
/-! P2 native block <-> product carrier equivalence status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2NativeProductEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P2NativeBlockAlignmentActual
def nativeProductEquivRows : List String :=
  [ "native block = qVFamTensorBlock (green)",
    "product carrier = finite product of root extensions",
    "no canonical equivalence/log-volume transport" ]
theorem nativeProductEquivRows_length : nativeProductEquivRows.length = 3 := rfl
def nativeProductEquivMissing : List String :=
  [ "explicit equivalence tensor block -> product carrier",
    "Haar det/log-volume transport" ]
theorem nativeProductEquivMissing_length : nativeProductEquivMissing.length = 2 := rfl

/-- Actual native block is the qVFam tensor block. -/
theorem nativeProductEquiv_nativeBlock {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) :
    qVFamTensorBlock T b =
      ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P2NativeProductEquivActual
end
