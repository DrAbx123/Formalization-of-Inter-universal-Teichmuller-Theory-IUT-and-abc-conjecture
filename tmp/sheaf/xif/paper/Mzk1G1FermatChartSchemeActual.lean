/- G1a Fermat chart schemes from AdjoinRoot monic bases. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatChartRingActual2
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic
noncomputable section
open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartRingActual2
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartSchemeActual
variable (n : Nat)
abbrev ChartU0 : Scheme := Spec (CommRingCat.of (fermatU0Ring n))
abbrev ChartU1 : Scheme := Spec (CommRingCat.of (fermatU1Ring n))
def chartU0ToSpec : ChartU0 n ⟶ Spec (CommRingCat.of (Polynomial ℚ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (fermatU0Ring n)))
def chartU1ToSpec : ChartU1 n ⟶ Spec (CommRingCat.of (Polynomial ℚ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (fermatU1Ring n)))
theorem fermatU0Ring_finrank (hn : 0 < n) :
    Module.finrank (Polynomial ℚ) (fermatU0Ring n) = n := by
  rw [Module.finrank_eq_card_basis (fermatU0Basis n hn)]
  rw [fermatU0Poly, Polynomial.natDegree_X_pow_sub_C]
  simp
theorem fermatU1Ring_finrank (hn : 0 < n) :
    Module.finrank (Polynomial ℚ) (fermatU1Ring n) = n := by
  rw [Module.finrank_eq_card_basis (fermatU1Basis n hn)]
  rw [fermatU1Poly, Polynomial.natDegree_X_pow_sub_C]
  simp
#print axioms fermatU0Ring_finrank
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartSchemeActual
