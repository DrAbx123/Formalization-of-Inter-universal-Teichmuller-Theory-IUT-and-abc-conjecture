import tmp.sheaf.xif.paper.S3128Stage1HDDFirstFieldEquivConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEquivConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldDownstreamConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDFirstField_symm_apply
    (F : S1300HDDFirstField I) :
    (S3128Stage1HDDFirstFieldEquiv (I := I)).symm
      ((S3128Stage1HDDFirstFieldEquiv (I := I)) F) = F :=
  S3128Stage1HDDFirstFieldEquiv_apply_symm (I := I) F

theorem S3128Stage1HDDFirstField_apply_symm
    (L : S1215HDDLocalLattice (I := I)) :
    S3128Stage1HDDFirstFieldEquiv (I := I)
      ((S3128Stage1HDDFirstFieldEquiv (I := I)).symm L) = L :=
  (S3128Stage1HDDFirstFieldEquiv (I := I)).apply_symm_apply L

theorem S3128Stage1HDDFirstField_rank
    (F : S1300HDDFirstField I) :
    (S3128Stage1HDDFirstFieldEquiv (I := I) F).rank = F.rank := rfl

theorem S3128Stage1HDDFirstField_lattice
    (F : S1300HDDFirstField I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    (S3128Stage1HDDFirstFieldEquiv (I := I) F).lattice o v =
      F.lattice o v := rfl

#check S3128Stage1HDDFirstField_symm_apply
#check S3128Stage1HDDFirstField_apply_symm
#check S3128Stage1HDDFirstField_rank
#check S3128Stage1HDDFirstField_lattice
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldDownstreamConsumerActual