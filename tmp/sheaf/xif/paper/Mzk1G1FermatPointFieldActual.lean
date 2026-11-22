import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPointFieldActual
open Polynomial

/-- The actual point algebra obtained by adjoining an `n`-th root of `a`:
`ℚ[y]/(y^n - a)`. -/
abbrev FermatPointAlgebra (a : ℚ) (n : ℕ) : Type :=
  AdjoinRoot (Polynomial.X ^ n - Polynomial.C a : Polynomial ℚ)

theorem fermatPointAlgebra_finrank {a : ℚ} {n : ℕ} (hn : n ≠ 0) :
    Module.finrank ℚ (FermatPointAlgebra a n) = n := by
  have hmonic : (Polynomial.X ^ n - Polynomial.C a : Polynomial ℚ).Monic :=
    Polynomial.monic_X_pow_sub_C a hn
  change Module.finrank ℚ (AdjoinRoot (Polynomial.X ^ n - Polynomial.C a : Polynomial ℚ)) = n
  rw [(AdjoinRoot.powerBasis' hmonic).finrank]
  exact Polynomial.natDegree_X_pow_sub_C

/-- The actual point algebra has the expected algebraic degree `n`. -/
theorem fermatPointAlgebra_degree_le {a : ℚ} {n : ℕ} (hn : n ≠ 0) :
    Module.finrank ℚ (FermatPointAlgebra a n) ≤ n :=
  le_of_eq (fermatPointAlgebra_finrank hn)

#print axioms fermatPointAlgebra_finrank
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPointFieldActual