import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import tmp.sheaf.xif.paper.S2014DicksonClassificationActual
open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual

lemma units_five_eq_one (u : K5ˣ) (h : u ^ 5 = 1) : u = 1 := by
  have hdvd5 : orderOf u ∣ 5 := by rw [orderOf_dvd_iff_pow_eq_one]; exact h
  have hdvd4 : orderOf u ∣ 4 := by
    have h4 : Nat.card K5ˣ = 4 := by rw [Nat.card_eq_fintype_card]; decide
    rw [← h4]
    exact orderOf_dvd_natCard u
  have hdvd1 : orderOf u ∣ 1 := by
    simpa using Nat.dvd_gcd hdvd5 hdvd4
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

lemma det_eq_one_of_order_five (a : GL2) (ha : orderOf a = 5) :
    (a : Mat).det = 1 := by
  have ha5 : a ^ 5 = 1 := by simpa [ha] using pow_orderOf_eq_one a
  have hdet5 : Matrix.GeneralLinearGroup.det a ^ 5 = 1 := by
    rw [← map_pow, ha5, map_one]
  have hdet1 : Matrix.GeneralLinearGroup.det a = 1 := units_five_eq_one _ hdet5
  exact congrArg Units.val hdet1


lemma line_image_eq_e1 (h : GL2) (v : V2) (hv : v ≠ 0)
    (hp : pairAct h ⟨normalize v, normalize_isRep v hv⟩ = ⟨![1, 0], by decide⟩) :
    h • v = ![1, 0] ∨ h • v = -![1, 0] := by
  have hp' : normalize (h • normalize v) = ![1, 0] := by
    have h := congrArg Subtype.val hp
    simpa [pairAct] using h
  have h1 : h • normalize v = ![1, 0] ∨ h • normalize v = -![1, 0] := by
    rcases normalize_eq_or_neg (h • normalize v) with hw | hw
    · left; rw [hw] at hp'; exact hp'
    · right
      have hneg : -(h • normalize v) = ![1, 0] := by rw [← hw]; exact hp'
      simpa using congrArg Neg.neg hneg
  rcases h1 with hw | hw <;> rcases normalize_eq_or_neg v with hv' | hv'
  · left; rw [hv'] at hw; exact hw
  · right
    rw [hv'] at hw
    have hneg : -(h • v) = ![1, 0] := by simpa using hw
    simpa using congrArg Neg.neg hneg
  · right; rw [hv'] at hw; exact hw
  · left
    rw [hv'] at hw
    have hneg : -(h • v) = -![1, 0] := by simpa using hw
    simpa using congrArg Neg.neg hneg

end LeanFormal.IUT.XiFPaper.S2009DicksonActual