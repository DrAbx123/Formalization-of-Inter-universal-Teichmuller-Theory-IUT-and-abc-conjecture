import tmp.sheaf.xif.paper.S1300HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDLatticeEquivConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDHullDetSpec_holds :
    S1300ActualHullDetSpec :=
  s1300ActualHullDetSpec_holds

theorem S3128Stage1HDDLatticeEquiv_left
    (L : S1215HDDLocalLattice (I := I)) :
    S1300HDDFirstField.toLocalLattice (I := I)
      (S1300HDDFirstField.ofLocalLattice (I := I) L) = L :=
  S1300HDDFirstField.toLocalLattice_ofLocalLattice (I := I) L

theorem S3128Stage1HDDLatticeEquiv_right
    (F : S1300HDDFirstField I) :
    S1300HDDFirstField.ofLocalLattice (I := I)
      (S1300HDDFirstField.toLocalLattice (I := I) F) = F :=
  S1300HDDFirstField.ofLocalLattice_toLocalLattice (I := I) F

#check S3128Stage1HDDHullDetSpec_holds
#check S3128Stage1HDDLatticeEquiv_left
#check S3128Stage1HDDLatticeEquiv_right
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDLatticeEquivConsumerActual