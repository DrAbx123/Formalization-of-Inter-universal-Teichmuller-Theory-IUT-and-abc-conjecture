import tmp.sheaf.xif.paper.S1356HDDHullDetSourceActual
import tmp.sheaf.xif.paper.S1300HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceTypeConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDSourceType_eq :
    S1356HDDSourceRequired (I := I) =
      S1300HDDHullDetSource (I := I) := rfl

theorem S3128Stage1HDDSourceType_nonempty_iff :
    Nonempty (S1356HDDSourceRequired (I := I)) ↔
      Nonempty (S1300HDDHullDetSource (I := I)) := Iff.rfl

theorem S3128Stage1HDDLocalLatticeType_eq :
    S1300HDDLocalLatticeRequired (I := I) =
      S1215HDDLocalLattice (I := I) := rfl

theorem S3128Stage1HDDFirstFieldType_eq :
    S1300HDDFirstFieldRequired (I := I) =
      S1300HDDFirstField (I := I) := rfl

#check S3128Stage1HDDSourceType_eq
#check S3128Stage1HDDSourceType_nonempty_iff
#check S3128Stage1HDDLocalLatticeType_eq
#check S3128Stage1HDDFirstFieldType_eq
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceTypeConsumerActual