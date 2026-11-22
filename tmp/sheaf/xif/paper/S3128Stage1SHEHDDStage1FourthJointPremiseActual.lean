import tmp.sheaf.xif.paper.S3128Stage1SHEHDDStage1ActualBundle
import tmp.sheaf.xif.paper.S3128Stage1HDDReadoutSpecActual
import tmp.sheaf.xif.paper.S3128Stage1SHEHDDFourthJointU3APIActual
import tmp.sheaf.xif.paper.S3128Stage1SHECompositionConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDStage1ActualBundle
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDReadoutSpecActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointU3APIActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDStage1FourthJointPremiseActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Stage 1 fourth-joint premise assembled from the EXIT0 HDD/SHE bundle:
HDD lattice agreement, frozen spec, SHE log-shift, SHE readout=unit, and the
HDD readout spec all in one consumer contract. -/
structure S3128Stage1SHEHDDStage1FourthJointPremise
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) : Prop where
  hdd_lattice :
    ∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
      (D.toS1215 (I := I)).lattice o v = D.lattice o v
  frozen : HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}
  logShift :
    ∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)
  she_readout :
    ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
      C.sheLocalization.expression v o =
        (actualSHEOutput I).bundle.localization v unitSection
  hdd_readout_spec : S3128Stage1HDDReadoutSpec (I := I) D

theorem S3128Stage1SHEHDDStage1FourthJointPremise_ofActuals
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S3128Stage1SHEHDDStage1FourthJointPremise (I := I) (J := J) D C :=
  { hdd_lattice := fun o v =>
      S3128Stage1HDDLocalLatticeFromFourthJoint_lattice (I := I) (J := J) D C o v
    frozen := S3128Stage1HDDLocalLatticeFromFourthJoint_frozen (I := I) (J := J) D C
    logShift := fun m m' j =>
      S3128Stage1HDDLocalLatticeFromFourthJoint_logShift (I := I) (J := J) D C m m' j
    she_readout := fun v o =>
      S3128Stage1SHECompositionConsumer_readout_unit I J C v o
    hdd_readout_spec := S3128Stage1HDDReadoutSpec_ofSource (I := I) D }

#check S3128Stage1SHEHDDStage1FourthJointPremise
#check S3128Stage1SHEHDDStage1FourthJointPremise_ofActuals
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDStage1FourthJointPremiseActual