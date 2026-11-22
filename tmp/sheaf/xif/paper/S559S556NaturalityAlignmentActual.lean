import tmp.sheaf.xif.paper.S556QvPhiInputActual
import tmp.sheaf.xif.paper.S522QvPhiRamificationModelActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual
import tmp.sheaf.xif.paper.S480Example32InputActual
import tmp.sheaf.xif.paper.S533QvPhiSubmonoidActual
/-! # S559: align S491 divisor naturality with qvPhi ramification pullback
S491's aligned divisor naturality uses the constant-identity phi; S556's
required equation uses qvPhi's ramification-scaled pullback.  This file
records the exact mismatch and the needed relation; no naturality is faked. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S559S556NaturalityAlignmentActual
open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S533QvPhiSubmonoidActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open LeanFormal.IUT.XiFPaper.S533QvPhiSubmonoidActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open Iut.SourceModelFrobenioid
universe u
variable {K : Type u} [Field K]
/-- The qvPhi pullback is multiplication by the ramification index. -/
theorem qvPhiPullback_eq_mul
    (R : RamificationIndexData)
    {X Y : Example32SmallBase K} (f : X ⟶ Y)
    (x : ULift.{u+1} ℕ) :
    (qvPhiRamificationModel (K := K) R).pullback f x = (R.e f).val • x := by
  change uliftNatMulLeft (R.e f).val x = (R.e f).val • x
  ext
  simp [uliftNatMulLeft, nsmul_eq_mul]
/-- Exact missing datum: the S556 naturality statement itself. -/
def S556NaturalityAlignmentRequired (K : Type u) [Field K]
    (R : @RamificationIndexData K _)
    (V : @DvSmallValuationFamily K _) : Prop :=
  @S556DivisorNaturalityRequired K _ R V
end LeanFormal.IUT.XiFPaper.S559S556NaturalityAlignmentActual
