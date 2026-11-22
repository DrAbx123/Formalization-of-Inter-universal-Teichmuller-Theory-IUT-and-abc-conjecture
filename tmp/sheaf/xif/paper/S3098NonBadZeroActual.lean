import tmp.sheaf.xif.paper.S3092NonBadZeroAttemptActual
import tmp.sheaf.xif.paper.S2984XifInclusionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3092NonBadZeroAttemptActual
open LeanFormal.IUT.XiFPaper.S2984XifInclusionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3098NonBadZeroActual

variable {l : PrimeGeFive} {V : Type} [Fintype V]
variable {I : OriginalInput.{0,0,0,0,0} l V}
variable (R : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The per-place hull log is identically zero, because the real hull volume
is zero (S2984). -/
theorem S3098_hullLog_eq_zero (v : V) : S3092HullLog I R n v = 0 := by
  unfold S3092HullLog
  have h : (I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n)).toReal = 0 := by
    exact sourceRealHullVolume_eq_zero I v (R v) n
  rw [h, Real.log_zero]

/-- S3098: every place outside the bad range has zero hull log.  This is
unconditional, and in fact every place has zero hull log. -/
theorem S3098_nonBadZero
    (badToV : Bad (nativePlaceSelection T) -> V) :
    S3092NonBadZero I R n T badToV := by
  intro v _
  exact S3098_hullLog_eq_zero (I := I) R n v

/-- The S3096 target is vacuous: every place, bad or not, has zero hull log. -/
theorem S3098_all_places_zero (v : V) : S3092HullLog I R n v = 0 :=
  S3098_hullLog_eq_zero (I := I) R n v

#check S3098_hullLog_eq_zero
#check S3098_nonBadZero
#check S3098_all_places_zero
#print axioms S3098_hullLog_eq_zero
#print axioms S3098_nonBadZero

end LeanFormal.IUT.XiFPaper.S3098NonBadZeroActual
end