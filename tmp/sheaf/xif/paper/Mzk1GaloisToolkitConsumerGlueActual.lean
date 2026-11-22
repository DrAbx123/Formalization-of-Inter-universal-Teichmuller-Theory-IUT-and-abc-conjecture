import LeanFormal.IUT.IUTIII.Theorem311.GaloisConnectionOneSidedToolkit

/-! # Mzk1GaloisToolkitConsumerGlueActual — consumer forms of the one-sided (Ind3) toolkit

Small reference/glue module (no new mathematics): consumes the proved one-sided Galois /
(Ind3) toolkit (`logVolume_ind3_upperSemi_comp`, `linkTwoSidedFaces_comp`) in the
componentwise forms used by the Corollary 3.12 Step (xi) route.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GaloisToolkitConsumerGlueActual

open LeanFormal.IUT
open LeanFormal.IUT.OneSidedGaloisToolkit
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge

universe u v

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice]

/-- One-sided log-volume behaviour at the identity parameter: (Ind3) does not decrease
the log-volume. -/
theorem logVolume_ind3_upperSemi_zero
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (c : Choice) :
    Q.logVolume c <= Q.logVolume (P.ind3 0 c) := by
  simpa using logVolume_ind3_upperSemi_comp (P := P) Q 0 0 c

/-- One-sided log-volume behaviour at an arbitrary vertical parameter. -/
theorem logVolume_ind3_upperSemi_iterate
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (n : Nat) (c : Choice) :
    Q.logVolume c <= Q.logVolume (P.ind3 n c) := by
  simpa using logVolume_ind3_upperSemi_comp (P := P) Q 0 n c

/-- Nonarchimedean face of the sandwich: the possible image at the composite parameter
contains the original possible image. -/
theorem possibleImage_ind3_subset
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hN1 : K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q)
    (hA1 : K1K2BoundaryReduction.archimedeanTargetLift P Q)
    (m n : Nat) (c : Choice) :
    Q.possibleImage c ⊆ Q.possibleImage (P.ind3 (m + n) c) :=
  (linkTwoSidedFaces_comp (P := P) Q hN1 hA1 m n c).1

/-- Archimedean face of the sandwich: every element of the composite possible image is
dominated by an element of the original possible image. -/
theorem archimedean_lift_ind3
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (hN1 : K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q)
    (hA1 : K1K2BoundaryReduction.archimedeanTargetLift P Q)
    (m n : Nat) (c : Choice) {z : Real}
    (hz : z ∈ Q.possibleImage (P.ind3 (m + n) c)) :
    ∃ y, y ∈ Q.possibleImage c ∧ z <= y :=
  (linkTwoSidedFaces_comp (P := P) Q hN1 hA1 m n c).2 z hz

#check logVolume_ind3_upperSemi_zero
#check logVolume_ind3_upperSemi_iterate
#check possibleImage_ind3_subset
#check archimedean_lift_ind3

end LeanFormal.IUT.XiFPaper.Mzk1GaloisToolkitConsumerGlueActual
end
