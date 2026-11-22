import tmp.sheaf.xif.paper.S3128Stage1SHEHDDFourthJointPremiseFromActualsConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDReadoutSpecActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointPremiseFromActualsConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDReadoutSpecActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointHDDLinkActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1SHEHDDFourthJointHDDLink
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S3128Stage1HDDReadoutSpec (I := I) D
      ∧ S3128Stage1SHEHDDFourthJointPremiseFromActuals
          (I := I) (J := J) D C :=
  ⟨S3128Stage1HDDReadoutSpec_ofSource (I := I) D,
    S3128Stage1SHEHDDFourthJointPremiseFromActuals_holds (I := I) (J := J) D C⟩

theorem S3128Stage1SHEHDDFourthJointHDDLink_lattice
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).lattice o v = D.lattice o v :=
  (S3128Stage1SHEHDDFourthJointPremiseFromActuals_holds (I := I) (J := J) D C).hdd_lattice o v

#check S3128Stage1SHEHDDFourthJointHDDLink
#check S3128Stage1SHEHDDFourthJointHDDLink_lattice
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointHDDLinkActual