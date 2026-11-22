import tmp.sheaf.xif.paper.S3090S3091CorrectedPlaceActual
import tmp.sheaf.xif.paper.GlobalThetaPilotHullLogVolumeActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3090S3091CorrectedPlaceActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3092NonBadZeroAttemptActual

variable {l : PrimeGeFive} {V : Type} [Fintype V]
variable {I : OriginalInput l V}
variable (R : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The per-place hull log at a source place. -/
noncomputable def S3092HullLog
    (I : OriginalInput l V)
    (R : forall v : V, I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (v : V) : Real :=
  Real.log (I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n)).toReal

/-- Exact non-bad zero target: every place outside the image of badToV has
zero hull log. -/
def S3092NonBadZero
    (I : OriginalInput l V)
    (R : forall v : V, I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (T : SourceNativeInitialThetaData.{0} l)
    (badToV : Bad (nativePlaceSelection T) -> V) : Prop :=
  forall v : V, v ∉ Set.range badToV -> S3092HullLog I R n v = 0

/-- Conditional global reduction: if non-bad places have zero hull log and
badToV is injective, the global hull sum equals the sum over bad places. -/
theorem S3092_globalSum_of_nonBadZero
    (badToV : Bad (nativePlaceSelection T) -> V)
    (hinj : Function.Injective badToV)
    (hzero : S3092NonBadZero I R n T badToV) :
    globalThetaHullLogVolume (I := I) R n =
      ∑ b : Bad (nativePlaceSelection T), S3092HullLog I R n (badToV b) := by
  classical
  rw [globalThetaHullLogVolume_eq]
  symm
  calc
    (Finset.sum (Finset.univ : Finset (Bad (nativePlaceSelection T))) (fun b =>
        S3092HullLog I R n (badToV b)))
        = Finset.sum ((Finset.univ : Finset (Bad (nativePlaceSelection T))).image badToV)
            (fun v => S3092HullLog I R n v) := by
          rw [Finset.sum_image]
          intro x _ y _ hxy
          exact hinj hxy
    _ = Finset.sum (Finset.univ : Finset V)
          (fun v => S3092HullLog I R n v) := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro v _ hv
          exact hzero v (by simpa using hv)

#check S3092HullLog
#check S3092NonBadZero
#check S3092_globalSum_of_nonBadZero

end LeanFormal.IUT.XiFPaper.S3092NonBadZeroAttemptActual
end