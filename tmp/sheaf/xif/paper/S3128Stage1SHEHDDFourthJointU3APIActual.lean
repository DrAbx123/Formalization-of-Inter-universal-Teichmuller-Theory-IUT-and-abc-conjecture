import tmp.sheaf.xif.paper.S3128Stage1SHEHDDFourthJointPremiseFromActualsConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointPremiseFromActualsConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointU3APIActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The U3 HDD local lattice, reconstructed from the actual fourth-joint
premise instead of the blocked U3 file. -/
noncomputable def S3128Stage1HDDLocalLatticeFromFourthJoint
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S1215HDDLocalLattice (I := I) :=
  D.toS1215

theorem S3128Stage1HDDLocalLatticeFromFourthJoint_lattice
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (S3128Stage1HDDLocalLatticeFromFourthJoint (I := I) (J := J) D C).lattice o v =
      D.lattice o v :=
  (S3128Stage1SHEHDDFourthJointPremiseFromActuals_holds (I := I) (J := J) D C).hdd_lattice o v

theorem S3128Stage1HDDLocalLatticeFromFourthJoint_frozen
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0} :=
  (S3128Stage1SHEHDDFourthJointPremiseFromActuals_holds (I := I) (J := J) D C).frozen

theorem S3128Stage1HDDLocalLatticeFromFourthJoint_logShift
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (m m' : Int) (j : SignedLabel l.value) :
    Real.log (J.oneColumnScale m j) =
      Real.log (J.oneColumnScale m' j) :=
  (S3128Stage1SHEHDDFourthJointPremiseFromActuals_holds (I := I) (J := J) D C).logShift m m' j

#check S3128Stage1HDDLocalLatticeFromFourthJoint
#check S3128Stage1HDDLocalLatticeFromFourthJoint_lattice
#check S3128Stage1HDDLocalLatticeFromFourthJoint_frozen
#check S3128Stage1HDDLocalLatticeFromFourthJoint_logShift
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointU3APIActual