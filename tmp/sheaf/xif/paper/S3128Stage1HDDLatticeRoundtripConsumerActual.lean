import tmp.sheaf.xif.paper.S1300HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDLatticeRoundtripConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDLattice_rank_roundtrip
    (L : S1215HDDLocalLattice (I := I)) :
    (S1300HDDFirstField.toLocalLattice (I := I)
      (S1300HDDFirstField.ofLocalLattice (I := I) L)).rank = L.rank :=
  rfl

theorem S3128Stage1HDDLattice_lattice_roundtrip
    (L : S1215HDDLocalLattice (I := I))
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (S1300HDDFirstField.toLocalLattice (I := I)
      (S1300HDDFirstField.ofLocalLattice (I := I) L)).lattice o v =
      L.lattice o v :=
  rfl

theorem S3128Stage1HDDLattice_roundtrip
    (L : S1215HDDLocalLattice (I := I)) :
    S1300HDDFirstField.toLocalLattice (I := I)
      (S1300HDDFirstField.ofLocalLattice (I := I) L) = L :=
  S1300HDDFirstField.toLocalLattice_ofLocalLattice (I := I) L

#check S3128Stage1HDDLattice_rank_roundtrip
#check S3128Stage1HDDLattice_lattice_roundtrip
#check S3128Stage1HDDLattice_roundtrip
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDLatticeRoundtripConsumerActual