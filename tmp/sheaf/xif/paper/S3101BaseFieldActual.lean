import tmp.sheaf.xif.paper.S3101IndexAuditActual
import tmp.sheaf.xif.paper.S2711PaperMultiUnconditionalActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3101IndexAuditActual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2706DirectHcompActual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3101BaseFieldActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)

/-- The S2717/S2711 concrete input has base field exactly GaussianField. -/
theorem S3101_S2711I_baseField_eq_gaussian :
    (S2711I R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.arithmetic.Fmod =
      GaussianField := by
  change (S2696SourceData fiveLabel R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).arithmetic.Fmod =
    GaussianField
  rw [S2696SourceData_arithmetic]
  rfl

/-- Exact base-field equivalence needed between S2717C3 and native T. -/
def S3101BaseFieldIso
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (T : SourceNativeInitialThetaData.{0} fiveLabel) : Prop :=
  Nonempty ((S2711I R redCompat hredCompat torCompat htorCompat orbCompat
    horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.arithmetic.Fmod ≃+*
      T.arithmetic.Fmod)

/-- The obstruction is exactly an isomorphism from the concrete Gaussian base
field to the native base field. -/
theorem S3101BaseFieldIso_iff
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (T : SourceNativeInitialThetaData.{0} fiveLabel) :
    S3101BaseFieldIso R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat T ↔
    Nonempty ((S2711I R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.arithmetic.Fmod ≃+*
        T.arithmetic.Fmod) := Iff.rfl

/-- Exact cardinal equality needed for a C3 tensor-index/native-bad index
equivalence. -/
def S3101IndexCardEquality
    (C3 : SourcePilotRegionData (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat))
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  Fintype.card C3.tensorIndex = Fintype.card (Bad (nativePlaceSelection T))

/-- Exact cardinal obstruction, as a Prop, not assumed. -/
def S3101IndexCardObstruction
    (C3 : SourcePilotRegionData (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat))
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  Fintype.card C3.tensorIndex ≠ Fintype.card (Bad (nativePlaceSelection T))

theorem S3101IndexEquivOfCard
    (C3 : SourcePilotRegionData (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat))
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (h : S3101IndexCardEquality R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat C3 T) :
    Nonempty (C3.tensorIndex ≃ Bad (nativePlaceSelection T)) :=
  ⟨Fintype.equivOfCardEq h⟩

#check S3101IndexEquivOfCard
#check S3101_S2711I_baseField_eq_gaussian
#check S3101BaseFieldIso
#check S3101BaseFieldIso_iff
#check S3101IndexCardEquality
#check S3101IndexCardObstruction
#print axioms S3101_S2711I_baseField_eq_gaussian
#print axioms S3101BaseFieldIso_iff

end LeanFormal.IUT.XiFPaper.S3101BaseFieldActual
end