import tmp.sheaf.xif.paper.S3128Stage1HDDFirstFieldEquivConsumerActual
import tmp.sheaf.xif.paper.S1300HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEquivConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldInjSurjConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDFirstFieldEquiv_injective :
    Function.Injective (S3128Stage1HDDFirstFieldEquiv (I := I)) :=
  (S3128Stage1HDDFirstFieldEquiv (I := I)).injective

theorem S3128Stage1HDDFirstFieldEquiv_surjective :
    Function.Surjective (S3128Stage1HDDFirstFieldEquiv (I := I)) :=
  (S3128Stage1HDDFirstFieldEquiv (I := I)).surjective

theorem S3128Stage1HDDFirstFieldEquiv_eq_iff
    (F F' : S1300HDDFirstField I) :
    S3128Stage1HDDFirstFieldEquiv (I := I) F =
      S3128Stage1HDDFirstFieldEquiv (I := I) F' ↔ F = F' :=
  (S3128Stage1HDDFirstFieldEquiv (I := I)).injective.eq_iff

theorem S3128Stage1HDDFirstFieldEquiv_symm_eq_iff
    (L L' : S1215HDDLocalLattice (I := I)) :
    (S3128Stage1HDDFirstFieldEquiv (I := I)).symm L =
      (S3128Stage1HDDFirstFieldEquiv (I := I)).symm L' ↔ L = L' :=
  (S3128Stage1HDDFirstFieldEquiv (I := I)).symm.injective.eq_iff

#check S3128Stage1HDDFirstFieldEquiv_injective
#check S3128Stage1HDDFirstFieldEquiv_surjective
#check S3128Stage1HDDFirstFieldEquiv_eq_iff
#check S3128Stage1HDDFirstFieldEquiv_symm_eq_iff
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldInjSurjConsumerActual