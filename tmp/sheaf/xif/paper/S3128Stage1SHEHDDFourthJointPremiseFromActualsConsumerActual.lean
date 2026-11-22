import tmp.sheaf.xif.paper.S3128Stage1SHECompositionConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1SHEHDDSpecActual
import tmp.sheaf.xif.paper.S3128Stage1HDDConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDCompositionConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDSpecActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDCompositionConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointPremiseFromActualsConsumerActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The U3 fourth-joint premise, built directly from the actual U16/U20/U73
components (no dependency on the blocked U3 file). -/
structure S3128Stage1SHEHDDFourthJointPremiseFromActuals
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) : Prop where
  hdd_lattice :
    ∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
      (D.toS1215 (I := I)).lattice o v = D.lattice o v
  frozen : HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}
  logShift :
    ∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)

theorem S3128Stage1SHEHDDFourthJointPremiseFromActuals_holds
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S3128Stage1SHEHDDFourthJointPremiseFromActuals (I := I) (J := J) D C :=
  { hdd_lattice := fun o v =>
      (S3128Stage1HDDConsumer_rank_lattice D).2 o v
    frozen := S3128Stage1HDDComposition_frozen
    logShift := fun m m' j =>
      S3128Stage1SHECompositionConsumer_logShift
        (l := l) (J := J) m m' j }

#check S3128Stage1SHEHDDFourthJointPremiseFromActuals
#check S3128Stage1SHEHDDFourthJointPremiseFromActuals_holds
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointPremiseFromActualsConsumerActual