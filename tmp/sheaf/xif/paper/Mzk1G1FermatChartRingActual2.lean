import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartRingActual2
open Polynomial
noncomputable def fermatU0Poly (n : Nat) : Polynomial (Polynomial ℚ) :=
  X ^ n - C (Polynomial.X)
theorem fermatU0Poly_monic (n : Nat) (hn : 0 < n) : (fermatU0Poly n).Monic := by
  unfold fermatU0Poly
  apply monic_X_pow_sub
  calc (C (Polynomial.X) : Polynomial (Polynomial ℚ)).degree ≤ 0 := degree_C_le
    _ < n := by exact_mod_cast hn
noncomputable def fermatU1Poly (n : Nat) : Polynomial (Polynomial ℚ) :=
  X ^ n - C (1 - Polynomial.X)
theorem fermatU1Poly_monic (n : Nat) (hn : 0 < n) : (fermatU1Poly n).Monic := by
  unfold fermatU1Poly
  apply monic_X_pow_sub
  calc (C (1 - Polynomial.X) : Polynomial (Polynomial ℚ)).degree ≤ 0 := degree_C_le
    _ < n := by exact_mod_cast hn
noncomputable abbrev fermatU0Ring (n : Nat) : Type := AdjoinRoot (fermatU0Poly n)
noncomputable abbrev fermatU1Ring (n : Nat) : Type := AdjoinRoot (fermatU1Poly n)
noncomputable def fermatU0Basis (n : Nat) (hn : 0 < n) :
    Module.Basis (Fin (fermatU0Poly n).natDegree) (Polynomial ℚ) (fermatU0Ring n) :=
  AdjoinRoot.powerBasisAux' (fermatU0Poly_monic n hn)
noncomputable def fermatU1Basis (n : Nat) (hn : 0 < n) :
    Module.Basis (Fin (fermatU1Poly n).natDegree) (Polynomial ℚ) (fermatU1Ring n) :=
  AdjoinRoot.powerBasisAux' (fermatU1Poly_monic n hn)
#print axioms fermatU0Poly_monic
#print axioms fermatU1Poly_monic
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartRingActual2
end