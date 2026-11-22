import tmp.sheaf.xif.paper.S3128Stage1HDDDetReadoutConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HullDetReadoutActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDDetReadoutConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HullDetReadoutActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDDetDownstreamActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}

theorem S3128Stage1HDDDetDownstream
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
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
    S3128Stage1HDDDetReadout_spec⟩

#check S3128Stage1HDDDetDownstream
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDDetDownstreamActual