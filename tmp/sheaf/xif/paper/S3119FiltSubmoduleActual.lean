import tmp.sheaf.xif.paper.S3119XLinearFromClassificationActual
import tmp.sheaf.xif.paper.S3119WeierstrassFiltrationActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
open LeanFormal.IUT.XiFPaper.S3119WeierstrassFiltrationActual
open LeanFormal.IUT.XiFPaper.S3119XCoordinateFixingTargets
open LeanFormal.IUT.XiFPaper.S3119XLinearFromClassificationActual
namespace LeanFormal.IUT.XiFPaper.S3119FiltSubmoduleActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
variable {l : PrimeGeFive}

lemma S3119_weightedDegree_zero :
    weightedDegree (0 : P l) = 0 := by
  rw [weightedDegree]
  simp

lemma S3119_weightedDegree_add_le (p q : P l) :
    weightedDegree (p + q) ≤ max (weightedDegree p) (weightedDegree q) := by
  rw [weightedDegree]
  apply Finset.sup_le
  intro m hm
  have hm' : m ∈ p.support ∪ q.support := MvPolynomial.support_add hm
  rcases Finset.mem_union.mp hm' with h | h
  · exact le_trans (Finset.le_sup (f := wdeg) h) (le_max_left _ _)
  · exact le_trans (Finset.le_sup (f := wdeg) h) (le_max_right _ _)

lemma S3119_weightedDegree_smul_le (a : S1348K l) (p : P l) :
    weightedDegree (a • p) ≤ weightedDegree p := by
  rw [weightedDegree]
  apply Finset.sup_le
  intro m hm
  exact Finset.le_sup (f := wdeg) (MvPolynomial.support_smul (a := a) (f := p) hm)

lemma S3119_weightedDegree_C_le (a : S1348K l) :
    weightedDegree (MvPolynomial.C a : P l) ≤ 0 := by
  rw [weightedDegree]
  apply Finset.sup_le
  intro m hm
  have hm0 : m = 0 := by
    by_contra h
    have hz : MvPolynomial.coeff m (MvPolynomial.C a) = 0 :=
      MvPolynomial.coeff_C_of_ne_zero h a
    exact (Finsupp.mem_support_iff.mp hm) hz
  subst hm0
  simp [wdeg]

lemma S3119_weightedDegree_one_le : weightedDegree (1 : P l) ≤ 2 := by
  have h := S3119_weightedDegree_C_le (l := l) (1 : S1348K l)
  rw [show weightedDegree (1 : P l) = 0 by simpa using h]
  exact Nat.zero_le 2

lemma S3119_weightedDegree_X0_le :
    weightedDegree (MvPolynomial.X (0 : Fin 2) : P l) ≤ 2 := by
  rw [weightedDegree_X0]

noncomputable def S3119filtSubmodule (n : ℕ) : Submodule (S1348K l) (P l) where
  carrier := filt n
  zero_mem' := by
    change weightedDegree (0 : P l) ≤ n
    rw [S3119_weightedDegree_zero]
    exact Nat.zero_le n
  add_mem' := by
    intro p q hp hq
    rw [filt] at *
    exact le_trans (S3119_weightedDegree_add_le p q) (max_le hp hq)
  smul_mem' := by
    intro a p hp
    rw [filt] at *
    exact le_trans (S3119_weightedDegree_smul_le a p) hp

lemma S3119_mem_filtSubmodule_two_iff (p : P l) :
    p ∈ S3119filtSubmodule (l := l) 2 ↔ weightedDegree p ≤ 2 := Iff.rfl

lemma S3119_span_le_filtSubmodule :
    Submodule.span (S1348K l) ({1, MvPolynomial.X (0 : Fin 2)} : Set (P l)) ≤
      S3119filtSubmodule (l := l) 2 := by
  rw [Submodule.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact S3119_weightedDegree_one_le
  · exact S3119_weightedDegree_X0_le

theorem S3119XImage_of_XLinear
    (h : S3119XLinearTarget (l := l)) :
    S3119XImageInFiltRTwoTarget (l := l) := by
  intro φ
  rcases h φ with ⟨a, b, hφ⟩
  rw [hφ]
  refine ⟨MvPolynomial.C a + b • MvPolynomial.X (0 : Fin 2), ?_, ?_⟩
  · apply S3119_span_le_filtSubmodule
    have h1 : (1 : P l) ∈ Submodule.span (S1348K l) ({1, MvPolynomial.X (0 : Fin 2)} : Set (P l)) :=
      Submodule.subset_span (by simp)
    have hx0 : (MvPolynomial.X (0 : Fin 2) : P l) ∈
        Submodule.span (S1348K l) ({1, MvPolynomial.X (0 : Fin 2)} : Set (P l)) :=
      Submodule.subset_span (by simp)
    have hC : (MvPolynomial.C a + b • MvPolynomial.X (0 : Fin 2) : P l) =
        a • (1 : P l) + b • MvPolynomial.X (0 : Fin 2) := by
      rw [MvPolynomial.C_eq_algebraMap, Algebra.algebraMap_eq_smul_one]
    rw [hC]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ hx0)
  · change (Ideal.Quotient.mkₐ (S1348K l) (Ideal.span {S1348AffinePolynomial l}))
        (MvPolynomial.C a + b • MvPolynomial.X (0 : Fin 2)) =
      algebraMap (S1348K l) (S1348CoordinateRing l) a +
        b • S3119x0 (l := l)
    rw [map_add, map_smul]
    rw [Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.C_eq_algebraMap, Ideal.Quotient.mk_algebraMap]

theorem S3119_filt_two_eq_span :
    filt (l := l) 2 =
      (Submodule.span (S1348K l) ({1, MvPolynomial.X (0 : Fin 2)} : Set (P l)) : Set (P l)) := by
  apply Set.Subset.antisymm
  · exact filt_two_le_span
  · intro x hx
    exact S3119_span_le_filtSubmodule hx

theorem S3119XLinear_of_XImage
    (h : S3119XImageInFiltRTwoTarget (l := l)) :
    S3119XLinearTarget (l := l) := by
  intro φ
  have hmem := h φ
  rw [S3119filtR] at hmem
  rcases hmem with ⟨p, hp, hEq⟩
  rw [S3119_filt_two_eq_span] at hp
  rcases Submodule.mem_span_pair.mp hp with ⟨a, b, hab⟩
  refine ⟨a, b, ?_⟩
  calc φ (S3119x0 (l := l)) = Ideal.Quotient.mk
        (Ideal.span {S1348AffinePolynomial l}) p := hEq.symm
    _ = Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
          (a • (1 : P l) + b • MvPolynomial.X (0 : Fin 2)) := by rw [hab]
    _ = algebraMap (S1348K l) (S1348CoordinateRing l) a +
          b • S3119x0 (l := l) := by
        change (Ideal.Quotient.mkₐ (S1348K l)
          (Ideal.span {S1348AffinePolynomial l}))
            (a • (1 : P l) + b • MvPolynomial.X (0 : Fin 2)) =
          algebraMap (S1348K l) (S1348CoordinateRing l) a +
            b • S3119x0 (l := l)
        rw [map_add, map_smul, map_smul, map_one]
        congr 1
        · exact (Algebra.algebraMap_eq_smul_one a).symm

def S3119PoleOrderLE (n : ℕ) (z : S1348CoordinateRing l) : Prop :=
  z ∈ S3119filtR (l := l) n

theorem S3119_x0_poleOrder_two :
    S3119PoleOrderLE (l := l) 2 (S3119x0 (l := l)) := by
  refine ⟨MvPolynomial.X (0 : Fin 2), ?_, rfl⟩
  rw [filt]
  exact le_of_eq (weightedDegree_X0 (l := l))

theorem S3119_y0_poleOrder_three :
    S3119PoleOrderLE (l := l) 3 (S3119y0 (l := l)) := by
  refine ⟨MvPolynomial.X (1 : Fin 2), ?_, rfl⟩
  rw [filt]
  exact le_of_eq (weightedDegree_X1 (l := l))

#check S3119PoleOrderLE
#check S3119_x0_poleOrder_two
#check S3119_y0_poleOrder_three
#print axioms S3119_x0_poleOrder_two
#print axioms S3119_y0_poleOrder_three
#check S3119_filt_two_eq_span
#check S3119XLinear_of_XImage
#print axioms S3119XLinear_of_XImage
#check S3119XImage_of_XLinear
#print axioms S3119XImage_of_XLinear
#check S3119filtSubmodule
#check S3119_span_le_filtSubmodule
#check S3119_weightedDegree_add_le
#check S3119_weightedDegree_smul_le
#check S3119_span_le_filtSubmodule
end LeanFormal.IUT.XiFPaper.S3119FiltSubmoduleActual
end
