import Mathlib

open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2579FactorDegreeActualAdapted

variable {K : Type*} [Field K] [Fintype K]

/-- An irreducible polynomial over a finite field divides X^(q^deg)-X. -/
theorem factor_degree_dvd {g : K[X]} (hg : Irreducible g) :
    g ∣ X ^ (Fintype.card K ^ g.natDegree) - X := by
  classical
  haveI : Fact (Irreducible g) := ⟨hg⟩
  let L := AdjoinRoot g
  haveI : Field L := inferInstance
  haveI : Fintype L := Fintype.ofFinite L
  let α : L := AdjoinRoot.root g
  have hfin : Module.finrank K L = g.natDegree := by
    change Module.finrank K (AdjoinRoot g) = g.natDegree
    rw [(AdjoinRoot.powerBasis hg.ne_zero).finrank]
  have hcard : Fintype.card L = Fintype.card K ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank, hfin]
  have hα : α ^ (Fintype.card L) = α := FiniteField.pow_card α
  have hα' : α ^ (Fintype.card K ^ g.natDegree) = α := by
    rwa [hcard] at hα
  have hzero : aeval α (X ^ (Fintype.card K ^ g.natDegree) - X) = 0 := by
    simp [map_sub, map_pow, hα']
  have hmin : minpoly K α ∣ X ^ (Fintype.card K ^ g.natDegree) - X :=
    minpoly.dvd K α hzero
  have hroot : minpoly K α = g * C (g.leadingCoeff⁻¹) := by
    rw [AdjoinRoot.minpoly_root hg.ne_zero]
    congr 1
    rw [mul_comm]
  rw [hroot] at hmin
  exact (dvd_mul_left g _).trans hmin

end LeanFormal.IUT.XiFPaper.S2579FactorDegreeActualAdapted
