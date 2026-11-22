import tmp.sheaf.xif.paper.S3128Stage1HDDFirstFieldEquivConsumerActual
import tmp.sheaf.xif.paper.S1300HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEquivConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldToS1215ConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDFirstFieldEquiv_toS1215
    (D : S1300HDDHullDetSource I) :
    S3128Stage1HDDFirstFieldEquiv (I := I)
      (S1300HDDFirstField.ofLocalLattice (I := I)
        (D.toS1215 (I := I))) =
      D.toS1215 (I := I) := by
  rw [← S3128Stage1HDDFirstFieldEquiv_invFun (I := I)]
  exact (S3128Stage1HDDFirstFieldEquiv (I := I)).apply_symm_apply
    (D.toS1215 (I := I))

theorem S3128Stage1HDDFirstFieldEquiv_symm_rank
    (D : S1300HDDHullDetSource I) :
    ((S3128Stage1HDDFirstFieldEquiv (I := I)).symm
      (D.toS1215 (I := I))).rank = D.rank := rfl

#check S3128Stage1HDDFirstFieldEquiv_toS1215
#check S3128Stage1HDDFirstFieldEquiv_symm_rank
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldToS1215ConsumerActual