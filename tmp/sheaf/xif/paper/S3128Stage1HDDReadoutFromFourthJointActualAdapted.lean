import tmp.sheaf.xif.paper.S3128SHEHDDInterfaceActual
import tmp.sheaf.xif.paper.S3128Stage1HDDDetReadoutConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128SHEHDDInterfaceActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDDetReadoutConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDReadoutFromFourthJointActualAdapted
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Stage 1 HDD readout assembled from the actual U3 fourth-joint premise
and the actual HDD/hull+det consumers. -/
theorem S3128Stage1HDDReadoutFromFourthJoint
    (D : S1300HDDHullDetSource I)
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).rank = D.rank
      ∧ (D.toS1215 (I := I)).lattice o v =
          (fun x : (i : Fin D.rank) → D.E i =>
            fun i => D.localEquiv v i (x i)) ''
          @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o)
      ∧ Nonempty
          (DetTensorPowerLogVolumeBookkeeping
            (Set ((i : Fin D.rank) → D.E i)))
      ∧ HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0} :=
  ⟨(S3128Stage1HDDConsumer_rank_lattice D).1,
    S3128Stage1HDDDetReadoutConsumer_hull D o v,
    S3128Stage1HDDDetReadoutConsumer_detBookkeeping D,
    (S3128Stage1SHEHDDFourthJointPremise_holds (I := I) (J := J) D).2.1⟩

#check S3128Stage1HDDReadoutFromFourthJoint
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDReadoutFromFourthJointActualAdapted