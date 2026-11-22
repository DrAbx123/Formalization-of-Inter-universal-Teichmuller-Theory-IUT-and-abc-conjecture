import tmp.sheaf.xif.paper.S1300HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDLatticeExtConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDLattice_ext
    (L L' : S1215HDDLocalLattice (I := I))
    (hrank : L.rank = L'.rank)
    (hlat : HEq L.lattice L'.lattice) :
    L = L' := by
  cases L with
  | mk r lat =>
    cases L' with
    | mk r' lat' =>
      simp only at hrank
      subst hrank
      have h : lat = lat' := eq_of_heq hlat
      subst h
      rfl

theorem S3128Stage1HDDLattice_ext_iff
    (L L' : S1215HDDLocalLattice (I := I)) :
    L = L' ↔
      ∃ hrank : L.rank = L'.rank, HEq L.lattice L'.lattice := by
  constructor
  · intro h
    subst h
    exact ⟨rfl, HEq.rfl⟩
  · rintro ⟨hrank, hlat⟩
    exact S3128Stage1HDDLattice_ext I L L' hrank hlat

#check S3128Stage1HDDLattice_ext
#check S3128Stage1HDDLattice_ext_iff
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDLatticeExtConsumerActual