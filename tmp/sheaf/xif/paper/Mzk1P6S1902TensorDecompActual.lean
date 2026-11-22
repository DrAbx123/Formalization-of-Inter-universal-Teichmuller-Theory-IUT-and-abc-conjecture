/- P6 S1902 tensor decomposition: uses the existing `PacketHullData` and the
actual `C3S1902BlockEquivData.blockEquiv`, without creating a new carrier. -/
import tmp.sheaf.xif.paper.Mzk1C3S1902BlockEquivDataActual
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902BlockEquivDataActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6S1902TensorDecompActual
universe u v w
variable {l : PrimeGeFive} {V : Type v}
variable (I : LeanFormal.IUT.Theorem311Source.OriginalInput l V)
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable {J : Type} [Finite J] {E : J -> Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[C3.p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[C3.p] (E j)] [∀ j, ProperSpace (E j)]
/-- The actual S1902 carrier tensor decomposition from the existing `C3S1902BlockEquivData`;
the carrier itself is not changed. -/
noncomputable def s1902TensorDecomp
    (B : C3S1902BlockEquivData I T C3) :
    S1902Carrier T ≃ C3LogShellTensorBlock C3 :=
  B.blockEquiv.symm

/-- Pointwise form of the actual S1902 tensor decomposition. -/
theorem s1902TensorDecomp_apply
    (B : C3S1902BlockEquivData I T C3) (x : S1902Carrier T) :
    s1902TensorDecomp (I := I) (T := T) C3 B x = B.blockEquiv.symm x := rfl

#check s1902TensorDecomp
#check s1902TensorDecomp_apply
end LeanFormal.IUT.XiFPaper.Mzk1P6S1902TensorDecompActual
end