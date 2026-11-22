import tmp.sheaf.xif.paper.S3076cWeightedProductAttempt

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3076cWeightedProductAttempt
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3076dNormProductBridgeAttempt

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem S3076d_theaterAt_expand :
    I.theaterAt 1 0 = I.family.theater (I.indexOf 1 0) := rfl

theorem S3076d_oneColumnQ_expand :
    I.oneColumnQAtZero =
      (I.family.theater (I.indexOf 1 0)).thetaPacket.q := rfl

theorem S3076d_family_q_const (i j : I.family.index) :
    (I.family.theater i).thetaPacket.q =
      (I.family.theater j).thetaPacket.q :=
  I.family.link_q i j

/-- The exact norm product statement, with the source q expanded to the
family theater packet q. -/
def S3076dNormProductStatement : Prop :=
  (I.family.theater (I.indexOf 1 0)).thetaPacket.q =
    ∏ b : Bad (nativePlaceSelection T),
      Real.exp (nativeBadLocalWeight T b *
        Real.log ‖(nativeBaseQFamily T b).q‖)

theorem S3076d_normProductStatement_iff :
    S3076dNormProductStatement (I := I) T ↔
      S3076cNormProductBridge (I := I) T := by
  unfold S3076dNormProductStatement S3076cNormProductBridge
  rw [S3076d_oneColumnQ_expand]

theorem S3076cNormProductBridge_of_statement
    (h : S3076dNormProductStatement (I := I) T) :
    S3076cNormProductBridge (I := I) T :=
  (S3076d_normProductStatement_iff (I := I) T).mp h

#check S3076d_theaterAt_expand
#check S3076d_oneColumnQ_expand
#check S3076d_family_q_const
#check S3076dNormProductStatement
#check S3076d_normProductStatement_iff
#print axioms S3076d_normProductStatement_iff

end LeanFormal.IUT.XiFPaper.S3076dNormProductBridgeAttempt
end
