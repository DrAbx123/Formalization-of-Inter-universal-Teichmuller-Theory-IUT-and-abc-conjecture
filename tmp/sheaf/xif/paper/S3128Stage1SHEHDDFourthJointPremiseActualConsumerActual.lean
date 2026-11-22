import tmp.sheaf.xif.paper.S3128Stage1SHEHDDFourthJointActualConsumerActual
import tmp.sheaf.xif.paper.S1385HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointActualConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointPremiseActualConsumerActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The U3 fourth-joint premise, obtained from the actual fresh data rather
than from the blocked U3 file. -/
structure S3128Stage1SHEHDDFourthJointPremiseActual
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) : Prop where
  hdd_lattice :
    ∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
      (D.toS1215 (I := I)).lattice o v = D.lattice o v
  frozen : HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}
  logShift :
    ∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)

theorem S3128Stage1SHEHDDFourthJointPremiseActual_ofActualData
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (H : S3128Stage1SHEHDDFourthJointActualData (I := I) (J := J) D C) :
    S3128Stage1SHEHDDFourthJointPremiseActual (I := I) (J := J) D C :=
  { hdd_lattice := H.hdd_lattice
    frozen := H.frozen
    logShift := H.she_logShift }

#check S3128Stage1SHEHDDFourthJointPremiseActual
#check S3128Stage1SHEHDDFourthJointPremiseActual_ofActualData
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointPremiseActualConsumerActual