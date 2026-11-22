import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import tmp.sheaf.xif.paper.S2014DicksonClassificationActual

noncomputable section
set_option maxHeartbeats 4000000
open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual

abbrev Cent (g : GL2) := Subgroup.centralizer ({g} : Set GL2)
abbrev Norm (g : GL2) := Subgroup.normalizer (Subgroup.zpowers g : Set GL2)

def matOf (M : Mat) (a b : K5) : Mat := a • (1 : Mat) + b • M
lemma matOf_inj (M : Mat) (hM : M * M + M + 1 = 0) {a b a' b' : K5}
    (h : matOf M a b = matOf M a' b') : a = a' ∧ b = b' := by
  have hc : M 1 0 ≠ 0 := entry10_ne_zero M hM
  have h10 : b * M 1 0 = b' * M 1 0 := by
    simpa [matOf] using congrFun (congrFun h 1) 0
  have h00 : a + b * M 0 0 = a' + b' * M 0 0 := by
    simpa [matOf] using congrFun (congrFun h 0) 0
  have hb : b = b' := mul_right_cancel₀ hc h10
  subst hb
  refine ⟨?_, rfl⟩
  linear_combination h00
lemma matOf_det_ne_zero (M : Mat) (hM : M * M + M + 1 = 0) (h3 : M * M * M = 1)
    {a b : K5} (hab : (a, b) ≠ 0) : (matOf M a b).det ≠ 0 := by
  have hd := det_smul_one_add_smul M h3 hM a b
  rw [matOf, hd]
  intro h0
  exact hab (by
    have hq := quad_form_ne_zero a b h0
    simpa using hq)
def glOf (M : Mat) (hM : M * M + M + 1 = 0) (h3 : M * M * M = 1)
    (a b : K5) (hab : (a, b) ≠ 0) : GL2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (matOf M a b) (matOf_det_ne_zero M hM h3 hab)
@[simp] lemma glOf_coe (M : Mat) (hM : M * M + M + 1 = 0) (h3 : M * M * M = 1)
    (a b : K5) (hab : (a, b) ≠ 0) :
    ((glOf M hM h3 a b hab : GL2) : Mat) = matOf M a b := rfl
lemma matOf_comm (M : Mat) (a b : K5) : matOf M a b * M = M * matOf M a b :=
  smul_one_add_smul_comm M a b
lemma glOf_mem_centralizer (M : Mat) (g : GL2) (hM : M * M + M + 1 = 0)
    (h3 : M * M * M = 1) (hgM : (g : Mat) = M) {a b : K5} (hab : (a, b) ≠ 0) :
    glOf M hM h3 a b hab ∈ Cent g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  simp only [Units.val_mul, glOf_coe, hgM]
  exact matOf_comm M a b
lemma mem_centralizer_exists (M : Mat) (g : GL2) (hM : M * M + M + 1 = 0)
    (h3 : M * M * M = 1) (hgM : (g : Mat) = M) {x : GL2}
    (hx : x ∈ Cent g) :
    ∃ a b : K5, ∃ (hab : (a, b) ≠ 0), x = glOf M hM h3 a b hab := by
  have hcomm : x * g = g * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hcommM : (x : Mat) * M = M * (x : Mat) := by
    have h := congrArg (fun y : GL2 => (y : Mat)) hcomm
    simpa [hgM] using h
  obtain ⟨a, b, hxab⟩ := cent_mem M hM (x : Mat) hcommM
  have hab : (a, b) ≠ 0 := by
    intro h0
    have hzero : (x : Mat) = 0 := by
      rw [hxab]
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h0
      simp
    exact Matrix.GeneralLinearGroup.det_ne_zero x (by rw [hzero]; simp)
  refine ⟨a, b, hab, ?_⟩
  apply Units.ext
  rw [hxab, glOf_coe]
  rfl

noncomputable def centEquiv (M : Mat) (g : GL2) (hM : M * M + M + 1 = 0)
    (h3 : M * M * M = 1) (hgM : (g : Mat) = M) :
    {v : K5 × K5 // v ≠ 0} ≃ Cent g :=
  Equiv.ofBijective
    (fun v => ⟨glOf M hM h3 v.1.1 v.1.2 v.2,
      glOf_mem_centralizer M g hM h3 hgM v.2⟩)
    ⟨by
      intro v w h
      apply Subtype.ext
      have hh : matOf M v.1.1 v.1.2 = matOf M w.1.1 w.1.2 := by
        have h' := congrArg (fun y : Cent g => ((y : GL2) : Mat)) h
        simpa using h'
      have hinj := matOf_inj M hM hh
      exact Prod.ext hinj.1 hinj.2,
     by
      intro x
      obtain ⟨a, b, hab, hx⟩ := mem_centralizer_exists M g hM h3 hgM x.2
      exact ⟨⟨(a, b), hab⟩, Subtype.ext hx.symm⟩⟩

lemma centralizer_card (M : Mat) (g : GL2) (hM : M * M + M + 1 = 0)
    (h3 : M * M * M = 1) (hgM : (g : Mat) = M) :
    Nat.card (Cent g) = 24 := by
  rw [← Nat.card_congr (centEquiv M g hM h3 hgM)]
  rw [Nat.card_eq_fintype_card]
  decide

def frobU (M : Mat) : K5 := (-1 - 2 * M 0 0) * (M 1 0)⁻¹
lemma frobU_spec (M : Mat) (hM : M * M + M + 1 = 0) :
    frobU M * M 1 0 = -1 - 2 * M 0 0 := by
  rw [frobU, mul_assoc, inv_mul_cancel₀ (entry10_ne_zero M hM), mul_one]
lemma frob_det_ne_zero (u : K5) : (frob u).det ≠ 0 := by
  simp [frob, Matrix.det_fin_two]
def frobGL (M : Mat) (hM : M * M + M + 1 = 0) : GL2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (frob (frobU M)) (frob_det_ne_zero (frobU M))
@[simp] lemma frobGL_coe (M : Mat) (hM : M * M + M + 1 = 0) :
    ((frobGL M hM : GL2) : Mat) = frob (frobU M) := rfl
lemma frobGL_sq (M : Mat) (hM : M * M + M + 1 = 0) :
    frobGL M hM * frobGL M hM = 1 := by
  apply Units.ext; simp [frobGL_coe, frob_sq]
lemma frobGL_conj (M : Mat) (g : GL2) (hM : M * M + M + 1 = 0) (hgM : (g : Mat) = M) :
    frobGL M hM * g = g ^ 2 * frobGL M hM := by
  apply Units.ext
  simp only [Units.val_mul, frobGL_coe, hgM, pow_two]
  exact frob_conj M hM (frobU M) (frobU_spec M hM)
lemma frobGL_inv (M : Mat) (hM : M * M + M + 1 = 0) :
    (frobGL M hM)⁻¹ = frobGL M hM :=
  inv_eq_of_mul_eq_one_right (frobGL_sq M hM)
lemma frobGL_conj' (M : Mat) (g : GL2) (hM : M * M + M + 1 = 0) (hgM : (g : Mat) = M) :
    frobGL M hM * g * (frobGL M hM)⁻¹ = g ^ 2 := by
  have h := frobGL_conj M g hM hgM
  rw [frobGL_inv]
  calc
    frobGL M hM * g * frobGL M hM = (frobGL M hM * g) * frobGL M hM := by rw [mul_assoc]
    _ = (g ^ 2 * frobGL M hM) * frobGL M hM := by rw [h]
    _ = g ^ 2 * (frobGL M hM * frobGL M hM) := by rw [mul_assoc]
    _ = g ^ 2 := by rw [frobGL_sq, mul_one]
lemma zpowers_sq_eq (g : GL2) (hg : orderOf g = 3) :
    Subgroup.zpowers (g ^ 2) = Subgroup.zpowers g := by
  have hg3 : g ^ 3 = 1 := by rw [← hg, pow_orderOf_eq_one]
  have hmem : g ∈ Subgroup.zpowers (g ^ 2) := by
    have hbinv : (g ^ 2)⁻¹ = g := by
      apply inv_eq_of_mul_eq_one_right
      simpa [pow_succ] using hg3
    have h := Subgroup.zpow_mem_zpowers (g ^ 2) (-1)
    simpa [zpow_neg_one, hbinv] using h
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact Subgroup.npow_mem_zpowers g 2
  · rw [Subgroup.zpowers_le]
    exact hmem
lemma frobGL_mem_normalizer (M : Mat) (g : GL2) (hM : M * M + M + 1 = 0)
    (hgM : (g : Mat) = M) (hg : orderOf g = 3) : frobGL M hM ∈ Norm g := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [MonoidHom.map_zpowers]
  have hconj : (MulAut.conj (frobGL M hM)) g = g ^ 2 := by
    simpa [MulAut.conj_apply] using frobGL_conj' M g hM hgM
  change Subgroup.zpowers ((MulAut.conj (frobGL M hM)) g) = Subgroup.zpowers g
  rw [hconj]
  exact zpowers_sq_eq g hg
lemma frobGL_not_mem_centralizer (M : Mat) (g : GL2) (hM : M * M + M + 1 = 0)
    (hgM : (g : Mat) = M) (hg : orderOf g = 3) : frobGL M hM ∉ Cent g := by
  intro hwC
  have hcomm : frobGL M hM * g = g * frobGL M hM :=
    Subgroup.mem_centralizer_singleton_iff.mp hwC
  have hconj := frobGL_conj' M g hM hgM
  have hgg : g ^ 2 = g := by
    calc g ^ 2 = frobGL M hM * g * (frobGL M hM)⁻¹ := hconj.symm
      _ = g := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hg1 : g = 1 := by
    have h := congrArg (fun y : GL2 => y * g⁻¹) hgg
    simpa [pow_two, mul_assoc] using h
  have hord : orderOf g = 1 := by rw [hg1, orderOf_one]
  rw [hg] at hord
  norm_num at hord

lemma centralizer_eq_zpowers (g : GL2) :
    Subgroup.centralizer (Subgroup.zpowers g : Set GL2) = Cent g := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
lemma cent_le_norm (g : GL2) : Cent g ≤ Norm g := by
  rw [← centralizer_eq_zpowers g]
  exact Subgroup.centralizer_le_normalizer _
lemma zpowers_three_cases (g : GL2) (hg : orderOf g = 3) {h : GL2}
    (hh : h ∈ Subgroup.zpowers g) : h = 1 ∨ h = g ∨ h = g ^ 2 := by
  have hx := (isOfFinOrder_of_finite g).mem_zpowers_iff_mem_range_orderOf.mp hh
  rw [hg] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  interval_cases n <;> simp
lemma orderOf_conj_eq (g : GL2) (x : GL2) : orderOf (x * g * x⁻¹) = orderOf g := by
  have hsem : SemiconjBy x g (x * g * x⁻¹) := by
    show x * g = (x * g * x⁻¹) * x
    group
  exact (SemiconjBy.orderOf_eq x hsem).symm
lemma normalizer_cases (g w : GL2) (hg : orderOf g = 3)
    (hw : w * g * w⁻¹ = g ^ 2) {x : GL2} (hx : x ∈ Norm g) :
    x ∈ Cent g ∨ ∃ c ∈ Cent g, x = w * c := by
  have hconjmem : x * g * x⁻¹ ∈ Subgroup.zpowers g := by
    rw [Subgroup.mem_set_normalizer_iff] at hx
    exact (hx g).mp (Subgroup.mem_zpowers g)
  rcases zpowers_three_cases g hg hconjmem with h1 | hg1 | hg2
  · exfalso
    have hord := orderOf_conj_eq g x
    rw [h1, orderOf_one, hg] at hord
    norm_num at hord
  · left
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * g = (x * g * x⁻¹) * x := by group
      _ = g * x := by rw [hg1]
  · right
    have hc : (w⁻¹ * x) * g * (w⁻¹ * x)⁻¹ = g := by
      calc (w⁻¹ * x) * g * (w⁻¹ * x)⁻¹ = w⁻¹ * (x * g * x⁻¹) * w := by group
        _ = w⁻¹ * g ^ 2 * w := by rw [hg2]
        _ = g := by
          calc w⁻¹ * g ^ 2 * w = w⁻¹ * (w * g * w⁻¹) * w := by rw [hw]
            _ = g := by group
    refine ⟨w⁻¹ * x, ?_, by group⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (w⁻¹ * x) * g = ((w⁻¹ * x) * g * (w⁻¹ * x)⁻¹) * (w⁻¹ * x) := by group
      _ = g * (w⁻¹ * x) := by rw [hc]

noncomputable def normalizerEquiv (g w : GL2) (hg : orderOf g = 3)
    (hw : w * g * w⁻¹ = g ^ 2) (hwN : w ∈ Norm g) (hwC : w ∉ Cent g) :
    Cent g × Bool ≃ Norm g :=
  Equiv.ofBijective
    (fun p : Cent g × Bool =>
      match p.2 with
      | false => ⟨(p.1 : GL2), cent_le_norm g p.1.2⟩
      | true => ⟨w * (p.1 : GL2), mul_mem hwN (cent_le_norm g p.1.2)⟩)
    ⟨by
      rintro ⟨p1, pb⟩ ⟨q1, qb⟩ hpq
      cases pb <;> cases qb
      · apply Prod.ext
        · apply Subtype.ext
          simpa using congrArg Subtype.val hpq
        · rfl
      · exfalso
        have h : (p1 : GL2) = w * (q1 : GL2) := by simpa using congrArg Subtype.val hpq
        have hw_eq : w = (p1 : GL2) * (q1 : GL2)⁻¹ := by rw [h]; group
        exact hwC (by rw [hw_eq]; exact mul_mem p1.2 (inv_mem q1.2))
      · exfalso
        have h : w * (p1 : GL2) = (q1 : GL2) := by simpa using congrArg Subtype.val hpq
        have hw_eq : w = (q1 : GL2) * (p1 : GL2)⁻¹ := by
          rw [← h]; group
        exact hwC (by rw [hw_eq]; exact mul_mem q1.2 (inv_mem p1.2))
      · apply Prod.ext
        · apply Subtype.ext
          exact mul_left_cancel (a := w) (by simpa using congrArg Subtype.val hpq)
        · rfl,
     by
      intro x
      rcases normalizer_cases g w hg hw x.2 with hxC | ⟨c, hcC, hxc⟩
      · refine ⟨(⟨x.1, hxC⟩, false), ?_⟩
        apply Subtype.ext
        rfl
      · refine ⟨(⟨c, hcC⟩, true), ?_⟩
        apply Subtype.ext
        exact hxc.symm⟩

lemma card_normalizer_of_cent (g w : GL2) (hg : orderOf g = 3)
    (hw : w * g * w⁻¹ = g ^ 2) (hwN : w ∈ Norm g) (hwC : w ∉ Cent g)
    (hC : Nat.card (Cent g) = 24) : Nat.card (Norm g) = 48 := by
  rw [← Nat.card_congr (normalizerEquiv g w hg hw hwN hwC)]
  rw [Nat.card_prod, hC]
  rw [Nat.card_eq_fintype_card]
  norm_num

theorem normalizerCard_proof : S2014NormalizerCard := by
  intro g hg
  let M : Mat := (g : Mat)
  have hg3 : g ^ 3 = 1 := by rw [← hg, pow_orderOf_eq_one]
  have h3M : M * M * M = 1 := by
    have h := congrArg (fun y : GL2 => (y : Mat)) hg3
    simpa [M, pow_three, mul_assoc] using h
  have h1M : M ≠ 1 := by
    intro h
    have hg1 : g = 1 := by
      apply Units.ext
      simpa [M] using h
    have hord : orderOf g = 1 := by rw [hg1, orderOf_one]
    rw [hg] at hord
    norm_num at hord
  have hM : M * M + M + 1 = 0 := mat_sq_add_self_add_one M h3M h1M
  have hgM : (g : Mat) = M := rfl
  have hw : frobGL M hM * g * (frobGL M hM)⁻¹ = g ^ 2 := frobGL_conj' M g hM hgM
  have hwN : frobGL M hM ∈ Norm g := frobGL_mem_normalizer M g hM hgM hg
  have hwC : frobGL M hM ∉ Cent g := frobGL_not_mem_centralizer M g hM hgM hg
  have hC : Nat.card (Cent g) = 24 := centralizer_card M g hM h3M hgM
  exact card_normalizer_of_cent g (frobGL M hM) hg hw hwN hwC hC

end LeanFormal.IUT.XiFPaper.S2009DicksonActual