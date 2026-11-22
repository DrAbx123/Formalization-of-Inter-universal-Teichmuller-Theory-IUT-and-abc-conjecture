import tmp.sheaf.xif.paper.S3128Stage1HDDFirstFieldEquivConsumerActual
import tmp.sheaf.xif.paper.S1300HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldEquivConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldBijectiveConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDFirstFieldEquiv_bijective :
    Function.Bijective (S3128Stage1HDDFirstFieldEquiv (I := I)) :=
  ⟨(S3128Stage1HDDFirstFieldEquiv (I := I)).injective,
    (S3128Stage1HDDFirstFieldEquiv (I := I)).surjective⟩

#check S3128Stage1HDDFirstFieldEquiv_bijective
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDFirstFieldBijectiveConsumerActual