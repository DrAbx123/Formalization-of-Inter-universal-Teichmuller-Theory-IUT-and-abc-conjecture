import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix
namespace S2009Probe11

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev V2 := Fin 2 → K5

abbrev IsRep (v : V2) : Prop :=
  (v 0 = 1 ∨ v 0 = 2) ∨ (v 0 = 0 ∧ (v 1 = 1 ∨ v 1 = 2))
abbrev PairRep := {v : V2 // IsRep v}

def normSign (v : V2) : K5 :=
  if v 0 = 1 ∨ v 0 = 2 then 1
  else if v 0 = 3 ∨ v 0 = 4 then -1
  else if v 1 = 1 ∨ v 1 = 2 then 1
  else -1
def normalize (v : V2) : V2 := normSign v • v

theorem normalize_isRep : ∀ v : V2, v ≠ 0 → IsRep (normalize v) := by decide
theorem normalize_eq_or_neg : ∀ v : V2, normalize v = v ∨ normalize v = -v := by decide
theorem normalize_neg : ∀ v : V2, normalize (-v) = normalize v := by decide
theorem normalize_of_isRep : ∀ v : V2, IsRep v → normalize v = v := by decide
theorem isRep_ne_zero : ∀ v : V2, IsRep v → v ≠ 0 := by decide

theorem smul_eq_zero_iff (g : GL2) (v : V2) : g • v = 0 ↔ v = 0 := by
  constructor
  · intro h
    exact Matrix.eq_zero_of_mulVec_eq_zero (Matrix.GeneralLinearGroup.det_ne_zero g) h
  · intro h
    rw [h]; simp

def pairAct (g : GL2) (x : PairRep) : PairRep :=
  ⟨normalize (g • x.1), normalize_isRep (g • x.1) (by
    intro h
    exact isRep_ne_zero x.1 x.2 ((smul_eq_zero_iff g x.1).mp h))⟩

theorem pairAct_one (x : PairRep) : pairAct 1 x = x := by
  apply Subtype.ext
  show normalize (1 • x.1) = x.1
  rw [one_smul, normalize_of_isRep x.1 x.2]

theorem normalize_smul_congr (g : GL2) {v w : V2} (h : w = v ∨ w = -v) :
    normalize (g • w) = normalize (g • v) := by
  rcases h with rfl | rfl
  · rfl
  · rw [show g • (-v) = -(g • v) by simp, normalize_neg]

theorem pairAct_mul (g h : GL2) (x : PairRep) :
    pairAct (g * h) x = pairAct g (pairAct h x) := by
  apply Subtype.ext
  show normalize ((g * h) • x.1) = normalize (g • normalize (h • x.1))
  rw [mul_smul]
  exact (normalize_smul_congr g (normalize_eq_or_neg (h • x.1))).symm

def pairEquiv (g : GL2) : PairRep ≃ PairRep where
  toFun := pairAct g
  invFun := pairAct g⁻¹
  left_inv x := by rw [← pairAct_mul, inv_mul_cancel, pairAct_one]
  right_inv x := by rw [← pairAct_mul, mul_inv_cancel, pairAct_one]

def pairPermHom : GL2 →* Equiv.Perm PairRep where
  toFun g := pairEquiv g
  map_one' := by apply Equiv.ext; intro x; exact pairAct_one x
  map_mul' g h := by apply Equiv.ext; intro x; exact pairAct_mul g h x

def g102 : GL2 := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 1] (by decide)

def repList : List PairRep :=
  [⟨![0, 1], by decide⟩,
   ⟨![1, 1], by decide⟩,
   ⟨![1, 2], by decide⟩,
   ⟨![2, 3], by decide⟩,
   ⟨![2, 0], by decide⟩,
   ⟨![0, 2], by decide⟩,
   ⟨![2, 2], by decide⟩,
   ⟨![2, 4], by decide⟩,
   ⟨![1, 4], by decide⟩,
   ⟨![1, 0], by decide⟩,
   ⟨![1, 3], by decide⟩,
   ⟨![2, 1], by decide⟩]

theorem repList_length : repList.length = 12 := by decide
theorem mem_repList : ∀ x : PairRep, x ∈ repList := by decide

def pairOf (i : Fin 12) : PairRep :=
  repList.get ⟨i.1, by rw [repList_length]; exact i.2⟩

def indexOf (x : PairRep) : Fin 12 :=
  ⟨repList.idxOf x, by
    have h := List.idxOf_lt_length_of_mem (mem_repList x)
    rwa [repList_length] at h⟩

theorem indexOf_pairOf : ∀ i : Fin 12, indexOf (pairOf i) = i := by decide
theorem pairOf_indexOf : ∀ x : PairRep, pairOf (indexOf x) = x := by decide

def pairEquivFin : PairRep ≃ Fin 12 where
  toFun := indexOf
  invFun := pairOf
  left_inv := pairOf_indexOf
  right_inv := indexOf_pairOf

theorem isCycle_permCongr {α β : Type*} {e : α ≃ β} {p : Equiv.Perm α}
    (hp : p.IsCycle) : (e.permCongr p).IsCycle := by
  obtain ⟨x, hx, h⟩ := hp
  refine ⟨e x, ?_, ?_⟩
  · intro hc
    apply hx
    have h1 : e (p x) = e x := by
      simpa [Equiv.permCongr_apply] using hc
    exact e.injective h1
  · intro y hy
    have hz : p (e.symm y) ≠ e.symm y := by
      intro hzy
      apply hy
      rw [Equiv.permCongr_apply, hzy, Equiv.apply_symm_apply]
    obtain ⟨n, hn⟩ := h hz
    refine ⟨n, ?_⟩
    have hmap : e.permCongr (p ^ n) = (e.permCongr p) ^ n := by
      simpa using map_zpow (Equiv.permCongrHom e) p n
    calc
      ((e.permCongr p) ^ n) (e x) = e.permCongr (p ^ n) (e x) := by rw [hmap]
      _ = e ((p ^ n) x) := by simp [Equiv.permCongr_apply]
      _ = e (e.symm y) := by rw [hn]
      _ = y := by simp

theorem support_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (p : Equiv.Perm α) :
    (e.permCongr p).support = p.support.map e.toEmbedding := by
  ext y
  simp only [Equiv.Perm.mem_support, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro h
    apply hy
    rw [Equiv.permCongr_apply, h, Equiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    simpa using hx

theorem card_support_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (p : Equiv.Perm α) :
    (e.permCongr p).support.card = p.support.card := by
  rw [support_permCongr]
  exact Finset.card_map _

def tau : Equiv.Perm (Fin 12) :=
  Fin.cycleRange (9 : Fin 12) * Equiv.swap (10 : Fin 12) (11 : Fin 12)

def C10 : Equiv.Perm PairRep := Equiv.permCongr (pairEquivFin.symm) (Fin.cycleRange (9 : Fin 12))
def C2 : Equiv.Perm PairRep := Equiv.permCongr (pairEquivFin.symm) (Equiv.swap (10 : Fin 12) (11 : Fin 12))
def C : Equiv.Perm PairRep := Equiv.permCongr (pairEquivFin.symm) tau

theorem card_support_cycleRange : (Fin.cycleRange (9 : Fin 12)).support.card = 10 := by
  rw [← Equiv.Perm.sum_cycleType, Fin.cycleType_cycleRange (by decide : (9 : Fin 12) ≠ 0)]
  simp

theorem C10_support_card : C10.support.card = 10 := by
  rw [C10, card_support_permCongr, card_support_cycleRange]

theorem C2_support_card : C2.support.card = 2 := by
  rw [C2, card_support_permCongr, Equiv.Perm.card_support_swap (by decide : (10 : Fin 12) ≠ 11)]

theorem C10_isCycle : C10.IsCycle := by
  rw [C10]
  exact isCycle_permCongr (Fin.isCycle_cycleRange (by decide : (9 : Fin 12) ≠ 0))

theorem C2_isCycle : C2.IsCycle := by
  rw [C2]
  exact isCycle_permCongr (Equiv.Perm.isCycle_swap (by decide : (10 : Fin 12) ≠ 11))

theorem pairAct_g102_pairOf : ∀ i : Fin 12, pairAct g102 (pairOf i) = pairOf (tau i) := by decide

theorem C_eq_pairPerm : C = pairPermHom g102 := by
  apply Equiv.ext
  intro x
  have hx : pairOf (indexOf x) = x := pairOf_indexOf x
  have hC : C (pairOf (indexOf x)) = pairOf (tau (indexOf x)) := by
    rw [C, tau]
    simp only [Equiv.permCongr_apply, Equiv.symm_symm]
    have hi : pairEquivFin (pairOf (indexOf x)) = indexOf x := indexOf_pairOf _
    rw [hi]
    rfl
  calc
    C x = C (pairOf (indexOf x)) := by rw [hx]
    _ = pairOf (tau (indexOf x)) := hC
    _ = pairPermHom g102 (pairOf (indexOf x)) := (pairAct_g102_pairOf (indexOf x)).symm
    _ = pairPermHom g102 x := by rw [hx]

theorem disjoint_support_cycleRange_swap :
    Disjoint (Fin.cycleRange (9 : Fin 12)).support (Equiv.swap (10 : Fin 12) (11 : Fin 12)).support := by
  decide

theorem disjoint_C10_C2 : Equiv.Perm.Disjoint C10 C2 := by
  rw [C10, C2, Equiv.Perm.disjoint_iff_disjoint_support, support_permCongr, support_permCongr, Finset.disjoint_map]
  exact disjoint_support_cycleRange_swap

theorem C10_mul_C2 : C10 * C2 = C := by
  rw [C10, C2, C, tau]
  rw [Equiv.permCongr_mul]

theorem cycleType_C : C.cycleType = ({10, 2} : Multiset ℕ) := by
  have hprod : ([C10, C2] : List (Equiv.Perm PairRep)).prod = C := by
    rw [← C10_mul_C2]
    simp
  have hcycle : ∀ σ : Equiv.Perm PairRep, σ ∈ [C10, C2] → σ.IsCycle := by
    intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl
    · exact C10_isCycle
    · exact C2_isCycle
  have hdisj : ([C10, C2] : List (Equiv.Perm PairRep)).Pairwise Equiv.Perm.Disjoint := by
    simp [disjoint_C10_C2]
  have h := Equiv.Perm.cycleType_eq (σ := C) [C10, C2] hprod hcycle hdisj
  rw [h]
  simp [C10_support_card, C2_support_card]
  rfl

theorem cycleType_pairPerm_g102 : (pairPermHom g102).cycleType = ({10, 2} : Multiset ℕ) := by
  rw [← C_eq_pairPerm]
  exact cycleType_C

end S2009Probe11