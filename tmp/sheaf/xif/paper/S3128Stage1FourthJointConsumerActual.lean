import tmp.sheaf.xif.paper.S1385HDDHullDetActual
import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointConsumerActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- SHE/HDD side of the fourth joint: readout = unit localization and the
actual frozen hull+det spec. -/
structure S3128Stage1FourthJointSHEHDD
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) : Prop where
  readout_eq_unit :
    ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
      C.sheLocalization.expression v o =
        (actualSHEOutput I).bundle.localization v unitSection
  frozen : HullDeterminantLogVolumeFrozenSpec

theorem S3128Stage1FourthJointSHEHDD_ofCompatibility
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S3128Stage1FourthJointSHEHDD (I := I) (J := J) C :=
  { readout_eq_unit := fun v o => by
      rw [C.readout_reference_compat, C.indeterminacy_sync]
    frozen := s1385FrozenSpec_actual }

/-- q-Theta comparison side of the fourth joint. -/
theorem S3128Stage1FourthJointComparison
    {V' : Type uv} [Fintype V']
    {I' : OriginalInput.{ua, uv, upi, umon, ui} l V'}
    (R : ∀ v : V', I'.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : GlobalComparisonCondition (I := I') R n) :
    qPilotThetaHullComparison (I := I') R n :=
  qPilotThetaHullComparison_of_condition (I := I') R n h

#check S3128Stage1FourthJointSHEHDD
#check S3128Stage1FourthJointSHEHDD_ofCompatibility
#check S3128Stage1FourthJointComparison
end LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointConsumerActual