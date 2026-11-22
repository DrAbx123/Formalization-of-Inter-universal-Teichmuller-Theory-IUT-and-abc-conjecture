import tmp.sheaf.xif.paper.S1300HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEquivConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

noncomputable def S3128Stage1HDDFirstFieldEquiv :
    S1300HDDFirstField I ≃ S1215HDDLocalLattice (I := I) :=
  S1300HDDFirstField.equivLocalLattice (I := I)

theorem S3128Stage1HDDFirstFieldEquiv_toFun
    (F : S1300HDDFirstField I) :
    S3128Stage1HDDFirstFieldEquiv (I := I) F =
      S1300HDDFirstField.toLocalLattice (I := I) F := rfl

theorem S3128Stage1HDDFirstFieldEquiv_invFun
    (L : S1215HDDLocalLattice (I := I)) :
    (S3128Stage1HDDFirstFieldEquiv (I := I)).symm L =
      S1300HDDFirstField.ofLocalLattice (I := I) L := rfl

theorem S3128Stage1HDDFirstFieldEquiv_apply_symm
    (F : S1300HDDFirstField I) :
    (S3128Stage1HDDFirstFieldEquiv (I := I)).symm
      ((S3128Stage1HDDFirstFieldEquiv (I := I)) F) = F :=
  (S3128Stage1HDDFirstFieldEquiv (I := I)).symm_apply_apply F

#check S3128Stage1HDDFirstFieldEquiv
#check S3128Stage1HDDFirstFieldEquiv_toFun
#check S3128Stage1HDDFirstFieldEquiv_invFun
#check S3128Stage1HDDFirstFieldEquiv_apply_symm
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEquivConsumerActual