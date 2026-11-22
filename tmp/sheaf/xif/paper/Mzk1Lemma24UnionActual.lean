import tmp.sheaf.xif.paper.Mzk1Lemma24GaloisUnion2Actual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24UnionActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnion2Actual

local instance decEqQbar : DecidableEq Qbar := Classical.decEq Qbar

/-- Reduced degree of an algebraic point alpha (paper [Mzk1] line 170):
[Q(alpha):Q] - 1 = natDegree(minpoly) - 1 (rational points have reduced degree 0). -/
def reducedDegreeOfPoint (α : Qbar) : Nat := (minpoly ℚ α).natDegree - 1

/-- m(S) for a finite nonempty set of algebraic points: the maximum reduced degree. -/
noncomputable def mOfPoints (S : Finset Qbar) (hne : S.Nonempty) : Nat :=
  (S.image reducedDegreeOfPoint).max' (hne.image reducedDegreeOfPoint)

/-- d(S): the sum of the reduced degrees equal to m(S) (paper lines 175-178). -/
noncomputable def dOfPoints (S : Finset Qbar) (hne : S.Nonempty) : Nat :=
  ∑ α ∈ S.filter (fun α => reducedDegreeOfPoint α = mOfPoints S hne),
    reducedDegreeOfPoint α

/-- Paper lines 177-178 on the point layer: d(S) = 0 iff m(S) = 0. -/
theorem s3135_dOfPoints_eq_zero_iff (S : Finset Qbar) (hne : S.Nonempty) :
    dOfPoints S hne = 0 ↔ mOfPoints S hne = 0 := by
  have himg : mOfPoints S hne ∈ S.image reducedDegreeOfPoint :=
    Finset.max'_mem (S.image reducedDegreeOfPoint) (hne.image reducedDegreeOfPoint)
  obtain ⟨α, hαS, hαm⟩ := Finset.mem_image.mp himg
  have hmem : α ∈ S.filter (fun β => reducedDegreeOfPoint β = mOfPoints S hne) := by
    rw [Finset.mem_filter]
    exact ⟨hαS, hαm⟩
  have hle : mOfPoints S hne ≤ dOfPoints S hne := by
    rw [← hαm]
    exact Finset.single_le_sum (f := fun β => reducedDegreeOfPoint β)
      (fun _ _ => Nat.zero_le _) hmem
  constructor
  · intro h
    omega
  · intro h
    unfold dOfPoints
    apply Finset.sum_eq_zero
    intro β hβ
    rw [Finset.mem_filter] at hβ
    rw [hβ.2, h]

/-- Galois-conjugate closure of a finite point set: the union of the finite conjugate
sets of its points (paper lines 166-169). -/
noncomputable def pointClosure (S : Finset Qbar) : Finset Qbar :=
  S.biUnion (fun α => (s3135_conjugateSet_finite α).toFinset)

/-- The point set is contained in its conjugate closure (self-membership). -/
theorem s3135_subset_pointClosure (S : Finset Qbar) : S ⊆ pointClosure S := by
  intro α hα
  rw [pointClosure, Finset.mem_biUnion]
  refine ⟨α, hα, ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact s3135_self_mem_conjugateSet α

#check s3135_dOfPoints_eq_zero_iff
#check s3135_subset_pointClosure
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24UnionActual
end