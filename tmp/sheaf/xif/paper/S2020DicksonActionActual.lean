import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Nat.Prime.Basic
import tmp.sheaf.xif.paper.S2020DicksonTransvectionActual
import tmp.sheaf.xif.paper.S2020DicksonNormalizerActual

noncomputable section
set_option maxHeartbeats 4000000
open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual

lemma sl_le_of_five_dvd (H : Subgroup GL2) (htrans : PairTransitive H)
    (h5 : 5 ∣ Nat.card H) :
    Subgroup.closure ({trv1, trv2} : Set GL2) ≤ H := by
  letI : Fintype H := Fintype.ofFinite H
  have h5' : 5 ∣ Fintype.card H := by simpa [Nat.card_eq_fintype_card] using h5
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card 5 h5'
  have haGL : orderOf (a : GL2) = 5 := by simpa using ha
  have hdet_a : ((a : GL2) : Mat).det = 1 := det_eq_one_of_order_five (a : GL2) haGL
  obtain ⟨v, hv, hav⟩ := orderFiveUnipotent_proof (a : GL2) haGL
  let vp : PairRep := ⟨normalize v, normalize_isRep v hv⟩
  let e1p : PairRep := ⟨![1, 0], by decide⟩
  obtain ⟨h1, hh1, hp1⟩ := htrans vp e1p
  have hline1 : h1 • v = ![1, 0] ∨ h1 • v = -![1, 0] := line_image_eq_e1 h1 v hv hp1
  let b1 : GL2 := h1 * (a : GL2) * h1⁻¹
  have hb1H : b1 ∈ H := by
    dsimp [b1]
    exact H.mul_mem (H.mul_mem hh1 a.2) (H.inv_mem hh1)
  have hb1fixv : b1 • (h1 • v) = h1 • v := by
    dsimp [b1]
    rw [mul_smul, mul_smul, inv_smul_smul, hav]
  have hb1fix : b1 • (![1, 0] : V2) = ![1, 0] := by
    rcases hline1 with hl | hl
    · rw [← hl]; exact hb1fixv
    · have hneg : b1 • (-( ![1, 0] : V2)) = -( ![1, 0] : V2) := by rw [← hl]; exact hb1fixv
      have hlin : b1 • (-( ![1, 0] : V2)) = -(b1 • (![1, 0] : V2)) := by rw [smul_neg]
      rw [hlin] at hneg
      exact neg_injective hneg
  have hb1det : (b1 : Mat).det = 1 := by
    have hda : Matrix.GeneralLinearGroup.det (a : GL2) = 1 := Units.ext hdet_a
    have hd : Matrix.GeneralLinearGroup.det b1 = 1 := by
      dsimp [b1]
      rw [map_mul, map_mul, map_inv, hda]
      simp
    exact congrArg Units.val hd
  have hb1ord : orderOf b1 = 5 := by
    dsimp [b1]
    rw [orderOf_conj_eq_normalizer (a : GL2) h1]
    exact haGL
  have hb1ne : b1 ≠ 1 := by
    intro hb
    have h1ord : orderOf b1 = 1 := by rw [hb, orderOf_one]
    rw [hb1ord] at h1ord
    norm_num at h1ord
  have htrv1 : trv1 ∈ H :=
    trv1_mem_of_fixes_e1 H b1 hb1H hb1fix hb1det hb1ne
  let e2p : PairRep := ⟨![0, 1], by decide⟩
  obtain ⟨h2, hh2, hp2⟩ := htrans vp e2p
  have hline2 : h2 • v = ![0, 1] ∨ h2 • v = -![0, 1] := line_image_eq_e2 h2 v hv hp2
  let b2 : GL2 := h2 * (a : GL2) * h2⁻¹
  have hb2H : b2 ∈ H := by
    dsimp [b2]
    exact H.mul_mem (H.mul_mem hh2 a.2) (H.inv_mem hh2)
  have hb2fixv : b2 • (h2 • v) = h2 • v := by
    dsimp [b2]
    rw [mul_smul, mul_smul, inv_smul_smul, hav]
  have hb2fix : b2 • (![0, 1] : V2) = ![0, 1] := by
    rcases hline2 with hl | hl
    · rw [← hl]; exact hb2fixv
    · have hneg : b2 • (-( ![0, 1] : V2)) = -( ![0, 1] : V2) := by rw [← hl]; exact hb2fixv
      have hlin : b2 • (-( ![0, 1] : V2)) = -(b2 • (![0, 1] : V2)) := by rw [smul_neg]
      rw [hlin] at hneg
      exact neg_injective hneg
  have hb2det : (b2 : Mat).det = 1 := by
    have hda : Matrix.GeneralLinearGroup.det (a : GL2) = 1 := Units.ext hdet_a
    have hd : Matrix.GeneralLinearGroup.det b2 = 1 := by
      dsimp [b2]
      rw [map_mul, map_mul, map_inv, hda]
      simp
    exact congrArg Units.val hd
  have hb2ord : orderOf b2 = 5 := by
    dsimp [b2]
    rw [orderOf_conj_eq_normalizer (a : GL2) h2]
    exact haGL
  have hb2ne : b2 ≠ 1 := by
    intro hb
    have h2ord : orderOf b2 = 1 := by rw [hb, orderOf_one]
    rw [hb2ord] at h2ord
    norm_num at h2ord
  have htrv2 : trv2 ∈ H :=
    trv2_mem_of_fixes_e2 H b2 hb2H hb2fix hb2det hb2ne
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | rfl
  · exact htrv1
  · exact htrv2


end LeanFormal.IUT.XiFPaper.S2009DicksonActual