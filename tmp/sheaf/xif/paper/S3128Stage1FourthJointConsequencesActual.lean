import tmp.sheaf.xif.paper.S3128Stage1SHEHDDFourthJointActualConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDDetReadoutConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1SHECompositionActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFourthJointActualConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDDetReadoutConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointConsequencesActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Consequences of the actual FourthJoint data: HDD rank/lattice, frozen
spec, det bookkeeping and the SHE composition premise. -/
theorem S3128Stage1FourthJointConsequences
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).rank = D.rank
      ∧ (D.toS1215 (I := I)).lattice o v = D.lattice o v
      ∧ HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}
      ∧ Nonempty
          (DetTensorPowerLogVolumeBookkeeping
            (Set ((i : Fin D.rank) → D.E i)))
      ∧ S3128Stage1SHECompositionPremise (J := J) :=
  let P := S3128Stage1SHEHDDFourthJointActualData_ofActuals (I := I) (J := J) D C
  ⟨P.hdd_rank,
    P.hdd_lattice o v,
    P.frozen,
    S3128Stage1HDDDetReadoutConsumer_detBookkeeping D,
    S3128Stage1SHECompositionPremise_holds (J := J)⟩

#check S3128Stage1FourthJointConsequences
end LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointConsequencesActual