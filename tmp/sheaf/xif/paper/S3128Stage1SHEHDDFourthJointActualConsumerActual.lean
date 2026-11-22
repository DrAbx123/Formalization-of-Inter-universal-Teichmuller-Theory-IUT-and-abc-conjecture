import tmp.sheaf.xif.paper.S3128Stage1SHECompositionConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1SHEHDDSpecActual
import tmp.sheaf.xif.paper.S3128Stage1HDDConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDCompositionConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDFirstFieldEquivConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDFirstFieldRoundtripConsumerActual
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
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEquivConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldRoundtripConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointActualConsumerActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

structure S3128Stage1SHEHDDFourthJointActualData
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) : Prop where
  she_readout :
    ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
      C.sheLocalization.expression v o =
        (actualSHEOutput I).bundle.localization v unitSection
  she_logShift :
    ∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)
  hdd_rank : (D.toS1215 (I := I)).rank = D.rank
  hdd_lattice :
    ∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
      (D.toS1215 (I := I)).lattice o v = D.lattice o v
  hdd_equiv :
    S3128Stage1HDDFirstFieldEquiv (I := I)
      (S1300HDDFirstField.ofLocalLattice (I := I)
        (D.toS1215 (I := I))) = D.toS1215 (I := I)
  frozen : HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}

theorem S3128Stage1SHEHDDFourthJointActualData_ofActuals
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S3128Stage1SHEHDDFourthJointActualData (I := I) (J := J) D C :=
  { she_readout := fun v o =>
      S3128Stage1SHECompositionConsumer_readout_unit I J C v o
    she_logShift := fun m m' j =>
      S3128Stage1SHECompositionConsumer_logShift (l := l) (J := J) m m' j
    hdd_rank := (S3128Stage1HDDConsumer_rank_lattice D).1
    hdd_lattice := fun o v => (S3128Stage1HDDConsumer_rank_lattice D).2 o v
    hdd_equiv := S3128Stage1HDDFirstField_apply_ofLocalLattice (I := I)
      (D.toS1215 (I := I))
    frozen := S3128Stage1HDDComposition_frozen }

#check S3128Stage1SHEHDDFourthJointActualData
#check S3128Stage1SHEHDDFourthJointActualData_ofActuals
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointActualConsumerActual