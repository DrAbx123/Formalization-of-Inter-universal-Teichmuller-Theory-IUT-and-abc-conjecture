import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Perfect
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace ProbeFact

theorem splittingField_finrank_dvd_factorial
    (K : Type*) [Field K] [CharZero K] (p : K[X]) :
    Module.finrank K p.SplittingField ∣ p.natDegree.factorial := by
  classical
  let L := p.SplittingField
  haveI : Fact ((p.map (algebraMap K L)).Splits) := ⟨SplittingField.splits p⟩
  haveI : Normal K L := Polynomial.SplittingField.instNormal p
  haveI : IsGalois K L := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hgal : Nat.card p.Gal = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  rw [← hgal]
  let φ := Polynomial.Gal.galActionHom p L
  have hφ : Function.Injective φ := Polynomial.Gal.galActionHom_injective p L
  let G := φ.range
  have h1 : Nat.card p.Gal = Nat.card G := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  rw [h1]
  have h2 : Nat.card G ∣ Nat.card (Equiv.Perm (p.rootSet L)) := Subgroup.card_subgroup_dvd_card G
  have h3 : Nat.card (Equiv.Perm (p.rootSet L)) = Nat.factorial (Nat.card (p.rootSet L)) := Nat.card_perm
  rw [h3] at h2
  have hcard_le : Nat.card (p.rootSet L) ≤ p.natDegree := by
    rw [Nat.card_eq_fintype_card]
    have h := Polynomial.ncard_rootSet_le p L
    rwa [← Set.fintypeCard_eq_ncard] at h
  have hfac : Nat.factorial (Nat.card (p.rootSet L)) ∣ Nat.factorial p.natDegree :=
    Nat.factorial_dvd_factorial hcard_le
  exact dvd_trans h2 hfac

example : Module.finrank ℚ (Polynomial.SplittingField (X^3 - 2 : ℚ[X])) ∣ Nat.factorial 3 := by
  simpa using splittingField_finrank_dvd_factorial ℚ (X^3 - 2 : ℚ[X])

end ProbeFact
