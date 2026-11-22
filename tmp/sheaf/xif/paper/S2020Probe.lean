import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Index
import tmp.sheaf.xif.paper.S2014DicksonClassificationActual

noncomputable section
set_option maxHeartbeats 4000000
open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) K5
def sl1 : SL2 := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (1 : K5)
def sl2 : SL2 := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (1 : K5)

lemma toGL_sl1 : ((sl1 : SL2) : GL2) = trv1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl1, trv1, Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.single]

lemma toGL_sl2 : ((sl2 : SL2) : GL2) = trv2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2, trv2, Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.single]

lemma transvection_zero_one_nat (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (n : K5) = sl1 ^ n := by
  induction n with
  | zero => simp [sl1]
  | succ n ih =>
      rw [Nat.cast_succ, Matrix.SpecialLinearGroup.transvection_add, ih, pow_succ]
      rfl

lemma transvection_one_zero_nat (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (n : K5) = sl2 ^ n := by
  induction n with
  | zero => simp [sl2]
  | succ n ih =>
      rw [Nat.cast_succ, Matrix.SpecialLinearGroup.transvection_add, ih, pow_succ]
      rfl

lemma transvection_mem_closure_zero_one (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (n : K5) ∈
      Subgroup.closure ({sl1, sl2} : Set SL2) := by
  rw [transvection_zero_one_nat]
  exact pow_mem (Subgroup.subset_closure (by simp [sl1])) n

lemma transvection_mem_closure_one_zero (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (n : K5) ∈
      Subgroup.closure ({sl1, sl2} : Set SL2) := by
  rw [transvection_one_zero_nat]
  exact pow_mem (Subgroup.subset_closure (by simp [sl2])) n

lemma transvection_mem_closure (i j : Fin 2) (hij : i ≠ j) (c : K5) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ Subgroup.closure ({sl1, sl2} : Set SL2) := by
  fin_cases i
  · fin_cases j
    · exact (hij rfl).elim
    · have hh : hij = (by decide : (0 : Fin 2) ≠ 1) := Subsingleton.elim _ _
      rw [hh, ← ZMod.natCast_zmod_val c]
      exact transvection_mem_closure_zero_one c.val
  · fin_cases j
    · have hh : hij = (by decide : (1 : Fin 2) ≠ 0) := Subsingleton.elim _ _
      rw [hh, ← ZMod.natCast_zmod_val c]
      exact transvection_mem_closure_one_zero c.val
    · exact (hij rfl).elim

lemma closure_sl_eq_top : Subgroup.closure ({sl1, sl2} : Set SL2) = ⊤ := by
  rw [eq_top_iff]
  intro A hA
  exact Matrix.SL2.transvection_induction
    (P := fun A => A ∈ Subgroup.closure ({sl1, sl2} : Set SL2))
    (fun i j hij c => transvection_mem_closure i j hij c)
    (fun A B hA hB => mul_mem hA hB) A

def slEquivKer : SL2 ≃ (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)).ker where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL A, by
    rw [MonoidHom.mem_ker]
    exact Matrix.SpecialLinearGroup.coeToGL_det A⟩
  invFun u := ⟨(u.1 : Mat), by
    have h := congrArg Units.val u.2
    simpa using h⟩
  left_inv A := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    rfl

lemma card_sl2 : Nat.card SL2 = 120 := by
  have hcard : Nat.card SL2 = Nat.card (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)).ker :=
    Nat.card_congr slEquivKer
  rw [hcard]
  have hsurj : Function.Surjective (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)) :=
    Matrix.GeneralLinearGroup.det_surjective
  have hidx : (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)).ker.index = 4 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    decide
  have hmul := Subgroup.index_mul_card (H := (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)).ker)
  rw [hidx, natCard_GL2] at hmul
  omega

def slEquivMap : SL2 ≃ (⊤ : Subgroup SL2).map Matrix.SpecialLinearGroup.toGL where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL A, by
    exact Subgroup.mem_map.mpr ⟨A, Subgroup.mem_top A, rfl⟩⟩
  invFun x := Classical.choose x.2
  left_inv A := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    exact (Classical.choose_spec (Subgroup.mem_map.mpr ⟨A, Subgroup.mem_top A, rfl⟩)).2
  right_inv x := by
    apply Subtype.ext
    exact (Classical.choose_spec x.2).2

lemma card_map_top : Nat.card ((⊤ : Subgroup SL2).map Matrix.SpecialLinearGroup.toGL) = 120 := by
  rw [← Nat.card_congr slEquivMap, card_sl2]

lemma closure_trv_eq_map : Subgroup.closure ({trv1, trv2} : Set GL2) =
    (Subgroup.closure ({sl1, sl2} : Set SL2)).map Matrix.SpecialLinearGroup.toGL := by
  have hset : ({trv1, trv2} : Set GL2) =
      Matrix.SpecialLinearGroup.toGL '' ({sl1, sl2} : Set SL2) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨sl1, Or.inl rfl, toGL_sl1⟩
      · exact ⟨sl2, Or.inr rfl, toGL_sl2⟩
    · rintro ⟨y, (rfl | rfl), hy⟩
      · left
        rw [← hy, toGL_sl1]
      · right
        rw [← hy, toGL_sl2]
  rw [hset, ← MonoidHom.map_closure]

lemma card_closure_trv : Nat.card (Subgroup.closure ({trv1, trv2} : Set GL2)) = 120 := by
  rw [closure_trv_eq_map, closure_sl_eq_top, card_map_top]

end LeanFormal.IUT.XiFPaper.S2009DicksonActual
