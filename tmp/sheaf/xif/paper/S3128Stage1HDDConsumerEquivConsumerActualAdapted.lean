import tmp.sheaf.xif.paper.S3128Stage1HDDConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDFirstFieldEquivConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDFirstFieldRoundtripConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEquivConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldRoundtripConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerEquivConsumerActualAdapted
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}

theorem S3128Stage1HDDConsumerEquiv_rank
    (D : S1300HDDHullDetSource I) :
    (D.toS1215 (I := I)).rank =
      (S3128Stage1HDDFirstFieldEquiv (I := I)
        (S1300HDDFirstField.ofLocalLattice (I := I)
          (D.toS1215 (I := I)))).rank := by
  rw [S3128Stage1HDDFirstFieldEquiv_rank]
  rfl

theorem S3128Stage1HDDConsumerEquiv_lattice
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).lattice o v =
      (S3128Stage1HDDFirstFieldEquiv (I := I)
        (S1300HDDFirstField.ofLocalLattice (I := I)
          (D.toS1215 (I := I)))).lattice o v := by
  rw [S3128Stage1HDDFirstField_apply_ofLocalLattice]

#check S3128Stage1HDDConsumerEquiv_rank
#check S3128Stage1HDDConsumerEquiv_lattice
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerEquivConsumerActualAdapted