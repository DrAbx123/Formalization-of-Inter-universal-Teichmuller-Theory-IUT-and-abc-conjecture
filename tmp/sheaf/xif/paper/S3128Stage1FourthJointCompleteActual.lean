import tmp.sheaf.xif.paper.S3128Stage1FourthJointSHEDataActual
import tmp.sheaf.xif.paper.S3128Stage1SHEHDDStage1FourthJointPremiseActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDStage1FourthJointPremiseActual
open LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointSHEDataActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointCompleteActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Closed consumer for the FourthJoint chain: the actual premise together
with the SHE data derived from it. -/
theorem S3128Stage1FourthJointComplete
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S3128Stage1SHEHDDStage1FourthJointPremise (I := I) (J := J) D C
      ∧ S3128Stage1FourthJointSHEData (I := I) (J := J) D C
          (S3128Stage1SHEHDDStage1FourthJointPremise_ofActuals (I := I) (J := J) D C) :=
  ⟨S3128Stage1SHEHDDStage1FourthJointPremise_ofActuals (I := I) (J := J) D C,
    S3128Stage1FourthJointSHEData_ofFourthJoint (I := I) (J := J) D C
      (S3128Stage1SHEHDDStage1FourthJointPremise_ofActuals (I := I) (J := J) D C)⟩

#check S3128Stage1FourthJointComplete
end LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointCompleteActual