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
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointPremiseDownstreamActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1SHEHDDFourthJointPremiseDownstream_conj
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    (∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
        (D.toS1215 (I := I)).lattice o v = D.lattice o v)
      ∧ HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}
      ∧ (∀ (m m' : Int) (j : SignedLabel l.value),
          Real.log (J.oneColumnScale m j) =
            Real.log (J.oneColumnScale m' j)) := by
  have P := S3128Stage1SHEHDDFourthJointPremiseFromActuals_holds (I := I) (J := J) D C
  exact ⟨P.hdd_lattice, P.frozen, P.logShift⟩

theorem S3128Stage1SHEHDDFourthJointPremiseDownstream_frozen
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0} :=
  (S3128Stage1SHEHDDFourthJointPremiseFromActuals_holds (I := I) (J := J) D C).frozen

theorem S3128Stage1SHEHDDFourthJointPremiseDownstream_lattice
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).lattice o v = D.lattice o v :=
  (S3128Stage1SHEHDDFourthJointPremiseFromActuals_holds (I := I) (J := J) D C).hdd_lattice o v

#check S3128Stage1SHEHDDFourthJointPremiseDownstream_conj
#check S3128Stage1SHEHDDFourthJointPremiseDownstream_frozen
#check S3128Stage1SHEHDDFourthJointPremiseDownstream_lattice
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointPremiseDownstreamActual