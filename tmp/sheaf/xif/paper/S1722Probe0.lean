import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Perfect
import Mathlib.Data.Finite.Perm

noncomputable section
open Polynomial

namespace ProbeCubic

variable (p : ℚ[X]) (hdeg : p.natDegree = 3)

example : Nat.factorial 3 ∣ 6 := by decide
example : Nat.factorial 2 ∣ 6 := by decide
example : Nat.factorial 1 ∣ 6 := by decide
example : Nat.factorial 0 ∣ 6 := by decide

example : Module.finrank ℚ p.SplittingField ∣ 6 := by
  classical
  let E := p.SplittingField
  haveI : Fact ((p.map (algebraMap ℚ E)).Splits) := ⟨SplittingField.splits p⟩
  haveI : Normal ℚ E := Polynomial.SplittingField.instNormal p
  haveI : IsGalois ℚ E := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hgal : Nat.card (p.Gal) = Module.finrank ℚ E := IsGalois.card_aut_eq_finrank ℚ E
  rw [← hgal]
  let φ := Polynomial.Gal.galActionHom p E
  have hφ : Function.Injective φ := Polynomial.Gal.galActionHom_injective p E
  let G := φ.range
  have h1 : Nat.card p.Gal = Nat.card G := by
    exact Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  rw [h1]
  have h2 : Nat.card G ∣ Nat.card (Equiv.Perm (p.rootSet E)) := Subgroup.card_subgroup_dvd_card G
  have h3 : Nat.card (Equiv.Perm (p.rootSet E)) = Nat.factorial (Nat.card (p.rootSet E)) := Nat.card_perm
  rw [h3] at h2
  have h4 : Nat.card (p.rootSet E) ≤ 3 := by
    rw [Nat.card_eq_fintype_card]
    have h := Polynomial.ncard_rootSet_le p E
    rw [← Set.fintypeCard_eq_ncard] at h
    rw [hdeg] at h
    exact h
  have h5 : Nat.factorial (Nat.card (p.rootSet E)) ∣ 6 := by
    interval_cases h : Nat.card (p.rootSet E) <;> decide
  exact dvd_trans h2 h5

end ProbeCubic
