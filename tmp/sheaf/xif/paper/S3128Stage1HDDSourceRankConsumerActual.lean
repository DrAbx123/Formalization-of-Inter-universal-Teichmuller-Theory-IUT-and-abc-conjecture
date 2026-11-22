import tmp.sheaf.xif.paper.S3128Stage1HDDFirstFieldEquivConsumerActual
import tmp.sheaf.xif.paper.S1356HDDHullDetSourceActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEquivConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceRankConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDSourceRank_rank
    (D : S1356HDDSourceRequired (I := I)) :
    (D.toS1215 (I := I)).rank = D.rank := rfl

theorem S3128Stage1HDDSourceRank_equiv_rank
    (D : S1356HDDSourceRequired (I := I)) :
    (S3128Stage1HDDFirstFieldEquiv (I := I)
      (S1300HDDFirstField.ofLocalLattice (I := I)
        (D.toS1215 (I := I)))).rank = D.rank := rfl

#check S3128Stage1HDDSourceRank_rank
#check S3128Stage1HDDSourceRank_equiv_rank
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceRankConsumerActual