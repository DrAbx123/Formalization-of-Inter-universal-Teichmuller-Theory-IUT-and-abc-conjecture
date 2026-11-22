import Mathlib
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Finite.Basic

/-!
# S2309: finite-field subfield uniqueness

For two intermediate fields A B of E/F with F finite and A finite-dimensional over F,
if Nat.card A = Nat.card B and A has positive F-degree, then A = B.  This is the
first missing lemma from S2307, proved by the polynomial X^(q^d) - X.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2309SubfieldUniqueActual

theorem finiteField_subfield_eq_of_card_eq
    {F E : Type*} [Field F] [Fintype F] [Field E] [Algebra F E]
    (A B : IntermediateField F E) [Fintype A] [Fintype B]
    (hdApos : 0 < Module.finrank F A)
    (hcard : Nat.card A = Nat.card B) : A = B := by
  classical
  let q := Nat.card F
  have hq2 : 2 ≤ q := by
    have h : 1 < Fintype.card F := Fintype.one_lt_card
    simpa [q, Nat.card_eq_fintype_card] using Nat.succ_le_of_lt h
  let dA := Module.finrank F A
  let dB := Module.finrank F B
  have hAcard : Nat.card A = q ^ dA := by
    simpa [q, dA, Nat.card_eq_fintype_card] using Module.natCard_eq_pow_finrank (K := F) (V := A)
  have hBcard : Nat.card B = q ^ dB := by
    simpa [q, dB, Nat.card_eq_fintype_card] using Module.natCard_eq_pow_finrank (K := F) (V := B)
  have hd : dA = dB := by
    have h : q ^ dA = q ^ dB := by rw [← hAcard, ← hBcard]; exact hcard
    exact Nat.pow_right_injective hq2 h
  let d := dA
  have hdpos : 0 < d := by simpa [d, dA] using hdApos
  have hAcard' : Nat.card A = q ^ d := by simpa [d, dA] using hAcard
  have hBcard' : Nat.card B = q ^ d := by simpa [d, hd, dB] using hBcard
  let p : E[X] := X ^ (q ^ d) - X
  have hN : 1 < q ^ d := Nat.one_lt_pow hdpos.ne' hq2
  have hpdeg : p.natDegree = q ^ d := by
    unfold p
    have hdegN : (X ^ (q ^ d) : E[X]).natDegree = q ^ d := natDegree_X_pow (q ^ d)
    have hdegX : (X : E[X]).natDegree = 1 := natDegree_X
    exact (natDegree_sub_eq_left_of_natDegree_lt (p := X ^ (q ^ d)) (q := X) (by
      rw [hdegN, hdegX]
      exact hN)).trans hdegN
  let S : Set E := p.rootSet E
  have hSle : S.ncard ≤ q ^ d := by
    exact (ncard_rootSet_le p E).trans_eq hpdeg
  have hA_sub : (A : Set E) ⊆ S := by
    intro x hx
    let xA : A := ⟨x, hx⟩
    have hpowA : xA ^ Nat.card A = xA := by
      simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card xA
    have hpowE : x ^ (q ^ d) = x := by
      have := congrArg Subtype.val hpowA
      rw [hAcard'] at this
      simpa [map_pow] using this
    rw [show S = p.rootSet E from rfl, mem_rootSet]
    constructor
    · intro hp0
      have hdeg := hpdeg
      rw [hp0, natDegree_zero] at hdeg
      have : 0 < q ^ d := pow_pos (by omega) _
      omega
    · simp [p, hpowE]
  have hAeqS : (A : Set E) = S := by
    apply Set.eq_of_subset_of_ncard_le hA_sub
    rw [show (A : Set E).ncard = Nat.card A from rfl, hAcard']
    exact hSle
  have hB_sub : (B : Set E) ⊆ S := by
    intro x hx
    let xB : B := ⟨x, hx⟩
    have hpowB : xB ^ Nat.card B = xB := by
      simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card xB
    have hpowE : x ^ (q ^ d) = x := by
      have := congrArg Subtype.val hpowB
      rw [hBcard'] at this
      simpa [map_pow] using this
    rw [show S = p.rootSet E from rfl, mem_rootSet]
    constructor
    · intro hp0
      have hdeg := hpdeg
      rw [hp0, natDegree_zero] at hdeg
      have : 0 < q ^ d := pow_pos (by omega) _
      omega
    · simp [p, hpowE]
  have hBeqS : (B : Set E) = S := by
    apply Set.eq_of_subset_of_ncard_le hB_sub
    rw [show (B : Set E).ncard = Nat.card B from rfl, hBcard']
    exact hSle
  ext x
  rw [show x ∈ A ↔ x ∈ (A : Set E) from Iff.rfl, hAeqS, ← hBeqS, show x ∈ (B : Set E) ↔ x ∈ B from Iff.rfl]

end LeanFormal.IUT.XiFPaper.S2309SubfieldUniqueActual
end
