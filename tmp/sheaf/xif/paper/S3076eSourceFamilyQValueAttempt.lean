import tmp.sheaf.xif.paper.S3088FamilyConstructionActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3088FamilyConstructionActual
open LeanFormal.IUT.XiFPaper.S3087GenericSourceHodgeFamilyAttempt
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3076eSourceFamilyQValueAttempt

variable {V : Type} [Fintype V] [Nonempty V]
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The S3088Family theater packet q is the constant `1`. -/
theorem S3076e_S3088_family_q_eq_one
    (A : InitialThetaArithmeticData.{0} fiveLabel) (i : SourceTheorem311Index) :
    ((S3088Family (V := V) A).theater i).thetaPacket.q = 1 := by
  simp [S3088Family, S3087Theater, sourceHaarActualThetaPacket,
    FiniteThetaPacket.ofQ_q]

/-- Native q norm is strictly below 1. -/
theorem S3076e_nativeQLog_neg (b : Bad (nativePlaceSelection T)) :
    Real.log ‖(nativeBaseQFamily T b).q‖ < 0 := by
  apply Real.log_neg
  · exact norm_pos_iff.mpr (nativeBaseQFamily_q_ne_zero T b)
  · exact LeanFormal.IUT.ArithmeticQPilotLogVolume.qNorm_lt_one (nativeBaseQFamily T b)

/-- With positive native weights, every product factor is below 1. -/
theorem S3076e_factor_lt_one (b : Bad (nativePlaceSelection T))
    (hw : 0 < nativeBadLocalWeight T b) :
    Real.exp (nativeBadLocalWeight T b *
      Real.log ‖(nativeBaseQFamily T b).q‖) < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact mul_neg_of_pos_of_neg hw (S3076e_nativeQLog_neg T b)

/-- No value relation: for the S3088Family q = 1, the norm product bridge
would force `1 = product`, which is impossible for nonempty bad family with
positive weights. -/
theorem S3076e_no_normProduct_of_S3088
    (hprod_lt :
      (∏ b : Bad (nativePlaceSelection T),
        Real.exp (nativeBadLocalWeight T b *
          Real.log ‖(nativeBaseQFamily T b).q‖)) < 1)
    [Nonempty (Bad (nativePlaceSelection T))] :
    (1 : Real) ≠
      ∏ b : Bad (nativePlaceSelection T),
        Real.exp (nativeBadLocalWeight T b *
          Real.log ‖(nativeBaseQFamily T b).q‖) := by
  linarith

#check S3076e_S3088_family_q_eq_one
#check S3076e_no_normProduct_of_S3088
#print axioms S3076e_S3088_family_q_eq_one
#print axioms S3076e_no_normProduct_of_S3088

end LeanFormal.IUT.XiFPaper.S3076eSourceFamilyQValueAttempt
end
