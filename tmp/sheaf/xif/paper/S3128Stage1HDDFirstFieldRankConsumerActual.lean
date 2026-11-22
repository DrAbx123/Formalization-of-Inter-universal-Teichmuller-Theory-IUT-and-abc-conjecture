import tmp.sheaf.xif.paper.S3128Stage1HDDFirstFieldEquivConsumerActual
import tmp.sheaf.xif.paper.S1300HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEquivConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldRankConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDFirstFieldEquiv_rank
    (F : S1300HDDFirstField I) :
    (S3128Stage1HDDFirstFieldEquiv (I := I) F).rank = F.rank := rfl

theorem S3128Stage1HDDFirstFieldEquiv_symm_rank
    (L : S1215HDDLocalLattice (I := I)) :
    ((S3128Stage1HDDFirstFieldEquiv (I := I)).symm L).rank = L.rank := rfl

theorem S3128Stage1HDDFirstFieldEquiv_rank_iff
    (F : S1300HDDFirstField I) (L : S1215HDDLocalLattice (I := I)) :
    (S3128Stage1HDDFirstFieldEquiv (I := I) F).rank = L.rank ↔
      F.rank = L.rank := by
  rw [S3128Stage1HDDFirstFieldEquiv_rank]

#check S3128Stage1HDDFirstFieldEquiv_rank
#check S3128Stage1HDDFirstFieldEquiv_symm_rank
#check S3128Stage1HDDFirstFieldEquiv_rank_iff
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldRankConsumerActual