import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2141D5FactorizationFieldsActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual

/-- The quadratic factor. -/
def S2141Factor2 : (ZMod 29)[X] := S2132Factor2

/-- The scaled degree-ten factor `4 * f`, written in expanded coefficient
form for the finite product computation. -/
def S2141Factor10 : (ZMod 29)[X] :=
  C (4 : ZMod 29) *
    (C 10 - C 5 * X - C 13 * X ^ 2 + C 14 * X ^ 3 - C 5 * X ^ 4 +
      C 8 * X ^ 5 + C 5 * X ^ 6 + C 7 * X ^ 7 - C 4 * X ^ 9 + X ^ 10)

/-- The small-coefficient mod-29 model of psi_5. -/
def S2141Psi5Mod29 : (ZMod 29)[X] :=
  C 16 + C 21 * X ^ 2 + C 21 * X ^ 3 + C 15 * X ^ 4 +
    C 1 * X ^ 5 + C 6 * X ^ 6 + C 24 * X ^ 7 + C 14 * X ^ 8 +
    C 10 * X ^ 9 + C 10 * X ^ 10 + C 8 * X ^ 11 + C 4 * X ^ 12

/-- Actual reduction of the explicit integer model to the small mod-29 model. -/
theorem S2141Reduction :
    S2132Psi5Z.map (Int.castRingHom (ZMod 29)) = S2141Psi5Mod29 := by
  ext n
  by_cases hn : n ≤ 12
  · interval_cases n <;> (simp [S2132Psi5Z, S2141Psi5Mod29] <;> decide)
  · have h1 : (S2132Psi5Z.map (Int.castRingHom (ZMod 29))).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simp [S2132Psi5Z]
      compute_degree!
      omega
    have h2 : S2141Psi5Mod29.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simp [S2141Psi5Mod29]
      compute_degree!
      omega
    rw [h1, h2]

/-- Actual product equality in the small mod-29 model. -/
theorem S2141ProductSmall :
    S2141Factor2 * S2141Factor10 = S2141Psi5Mod29 := by
  ext n
  by_cases hn : n ≤ 12
  · interval_cases n <;>
      (simp [S2141Factor2, S2141Factor10, S2132Factor2, S2141Psi5Mod29,
        coeff_add, coeff_sub, coeff_mul, coeff_C, coeff_X_pow, coeff_X] <;>
        reduce_mod_char <;> decide)
  · have hleft : (S2141Factor2 * S2141Factor10).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simp [S2141Factor2, S2141Factor10, S2132Factor2]
      compute_degree!
      omega
    have hright : S2141Psi5Mod29.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simp [S2141Psi5Mod29]
      compute_degree!
      omega
    rw [hleft, hright]

/-- Product equality against the explicit integer model. -/
theorem S2141Product :
    S2141Factor2 * S2141Factor10 =
      S2132Psi5Z.map (Int.castRingHom (ZMod 29)) := by
  rw [S2141Reduction]
  exact S2141ProductSmall

theorem S2141Factor2_natDegree : S2141Factor2.natDegree = 2 := by
  unfold S2141Factor2 S2132Factor2
  compute_degree!

theorem S2141Factor10_natDegree : S2141Factor10.natDegree = 10 := by
  unfold S2141Factor10
  compute_degree!

/-- Exact remaining global integer-model identification. -/
def S2141IntegerModelRequired : Prop :=
  S2132Psi5Z.map (Int.castRingHom ℚ) = S2057Psi5Q

/-- Exact remaining quadratic irreducibility. -/
def S2141QuadraticIrreducibleRequired : Prop :=
  Irreducible S2141Factor2

/-- Exact remaining degree-ten irreducibility, to be transferred from S2126
after identifying the expanded factor with S2132Factor10. -/
def S2141DegreeTenIrreducibleRequired : Prop :=
  Irreducible S2141Factor10

/-- Conditional assembly of S2057Mod29FactorizationData from the remaining
exact facts; the product and both degrees are actual. -/
noncomputable def s2141S2057Mod29Data_of
    (hmodel : S2141IntegerModelRequired)
    (h2irr : S2141QuadraticIrreducibleRequired)
    (h10irr : S2141DegreeTenIrreducibleRequired) :
    S2057Mod29FactorizationData where
  integerModel := S2132Psi5Z
  integerModel_map := hmodel
  factor2 := S2141Factor2
  factor10 := S2141Factor10
  product_eq := S2141Product
  factor2_irreducible := h2irr
  factor10_irreducible := h10irr
  factor2_degree := S2141Factor2_natDegree
  factor10_degree := S2141Factor10_natDegree

end LeanFormal.IUT.XiFPaper.S2141D5FactorizationFieldsActual

end
