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
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointU3APIActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDStage1ActualBundle
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Stage 1 HDD/SHE actual bundle: HDD lattice agreement, frozen spec,
log-shift and SHE readout=unit, all obtained from EXIT0 actual components. -/
theorem S3128Stage1SHEHDDStage1ActualBundle
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I)
    (m m' : Int) (j : SignedLabel l.value) :
    (D.toS1215 (I := I)).lattice o v = D.lattice o v
      ∧ HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}
      ∧ Real.log (J.oneColumnScale m j) =
          Real.log (J.oneColumnScale m' j)
      ∧ C.sheLocalization.expression v o =
          (actualSHEOutput I).bundle.localization v unitSection :=
  ⟨S3128Stage1HDDLocalLatticeFromFourthJoint_lattice (I := I) (J := J) D C o v,
    S3128Stage1HDDLocalLatticeFromFourthJoint_frozen (I := I) (J := J) D C,
    S3128Stage1HDDLocalLatticeFromFourthJoint_logShift (I := I) (J := J) D C m m' j,
    S3128Stage1SHECompositionConsumer_readout_unit I J C v o⟩

#check S3128Stage1SHEHDDStage1ActualBundle
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDStage1ActualBundle