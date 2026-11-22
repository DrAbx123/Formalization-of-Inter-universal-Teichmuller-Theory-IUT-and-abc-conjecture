import tmp.sheaf.xif.paper.S3128Stage1HDDFirstFieldEquivConsumerActual
import tmp.sheaf.xif.paper.S1300HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEquivConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEqSymmConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDFirstFieldEquiv_eq_symm_iff
    (F : S1300HDDFirstField I) (L : S1215HDDLocalLattice (I := I)) :
    S3128Stage1HDDFirstFieldEquiv (I := I) F = L ↔
      F = (S3128Stage1HDDFirstFieldEquiv (I := I)).symm L := by
  constructor
  · intro h
    rw [← h]
    exact ((S3128Stage1HDDFirstFieldEquiv (I := I)).symm_apply_apply F).symm
  · intro h
    rw [h]
    exact (S3128Stage1HDDFirstFieldEquiv (I := I)).apply_symm_apply L

theorem S3128Stage1HDDFirstFieldEquiv_symm_apply_eq_iff
    (L : S1215HDDLocalLattice (I := I)) (F : S1300HDDFirstField I) :
    (S3128Stage1HDDFirstFieldEquiv (I := I)).symm L = F ↔
      L = S3128Stage1HDDFirstFieldEquiv (I := I) F := by
  constructor
  · intro h
    rw [← h]
    exact ((S3128Stage1HDDFirstFieldEquiv (I := I)).apply_symm_apply L).symm
  · intro h
    rw [h]
    exact (S3128Stage1HDDFirstFieldEquiv (I := I)).symm_apply_apply F

#check S3128Stage1HDDFirstFieldEquiv_eq_symm_iff
#check S3128Stage1HDDFirstFieldEquiv_symm_apply_eq_iff
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEqSymmConsumerActual