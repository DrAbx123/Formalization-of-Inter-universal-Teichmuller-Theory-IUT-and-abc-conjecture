import tmp.sheaf.xif.paper.MultiradialProcessionActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1ProcessionAssocConsumerActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {A : CapsuleTheaterAssignment l V I}
variable {j : Fin (capsuleLevels l)}

/-- Consumer: procession transitions associate, using the actual
`PrcTransition_trans` law twice on each side. -/
theorem S3128Stage1PrcTransition_assoc
    (i i' i'' i''' : Capsule j.val) :
    FPrimeStripEquiv.trans
      (FPrimeStripEquiv.trans (PrcTransition A j i i')
        (PrcTransition A j i' i''))
      (PrcTransition A j i'' i''') =
    FPrimeStripEquiv.trans (PrcTransition A j i i')
      (FPrimeStripEquiv.trans (PrcTransition A j i' i'')
        (PrcTransition A j i'' i''')) := by
  rw [← PrcTransition_trans A j i i' i'',
    PrcTransition_trans A j i i'' i''',
    ← PrcTransition_trans A j i' i'' i''',
    PrcTransition_trans A j i i' i''']

/-- Consumer: the reversed transition composes back to the direct one. -/
theorem S3128Stage1PrcTransition_reverse
    (i i' : Capsule j.val) :
    FPrimeStripEquiv.trans (PrcTransition A j i i')
      (PrcTransition A j i' i) = PrcTransition A j i i :=
  PrcTransition_trans A j i i' i

#check S3128Stage1PrcTransition_assoc
#check S3128Stage1PrcTransition_reverse
end LeanFormal.IUT.XiFPaper.S3128Stage1ProcessionAssocConsumerActual