import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import tmp.sheaf.xif.paper.S2839A6F6ClauseRestatementActual
import tmp.sheaf.xif.paper.S2798StableEverywhere37Actual
import tmp.sheaf.xif.paper.S2786SignQuotientActual
import tmp.sheaf.xif.paper.S2766MaximalSolvableTopActual
import tmp.sheaf.xif.paper.S2782Curve37a1Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2790F6Actual
open LeanFormal.IUT.XiFPaper.S2782Curve37a1Actual
open LeanFormal.IUT.XiFPaper.S2787ClauseB37Actual
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
noncomputable section
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
example : S2847A6.curve.curve = E37QiPunctured.curve.baseChange S2847F6 := by
  ext <;> simp [S2847A6, S2847Curve, S2790E, S2790A, S2787Arithmetic, E37a1Q, E37a1CurveQ, E37QiPunctured, E37Qi, E37, PuncturedEllipticCurve.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]
example : S2847A6.curve.jInvariant = algebraMap ℚ S2847F6 (110592 / 37 : ℚ) := by
  change ((((E37a1Q.baseChange GaussianField).baseChange S2847F6).curve).j) =
    algebraMap ℚ S2847F6 (110592 / 37)
  rw [PuncturedEllipticCurve.baseChange, PuncturedEllipticCurve.baseChange]
  change (((E37.map (algebraMap ℚ GaussianField)).map
    (algebraMap GaussianField S2847F6)).j) = algebraMap ℚ S2847F6 (110592 / 37)
  rw [WeierstrassCurve.map_j, WeierstrassCurve.map_j, E37_j]
  exact (IsScalarTower.algebraMap_apply ℚ GaussianField S2847F6 (110592/37)).symm

example : S2847A6.curve.HasStableReductionEverywhere := by
  have hbase := PuncturedEllipticCurve.hasStableReductionEverywhere_baseChange
    (X := E37QiPunctured) (K := S2847F6) S2798_hasStableReductionEverywhere
  convert hbase using 1
  ext <;> simp [S2847A6, S2847Curve, S2790E, S2790A, S2787Arithmetic, E37a1Q,
    E37a1CurveQ, E37QiPunctured, E37Qi, E37, PuncturedEllipticCurve.baseChange,
    WeierstrassCurve.baseChange, WeierstrassCurve.map]
example : isFiniteSolvableGaloisSubextension (⊤ : IntermediateField S2847F6 S2847F6) :=
  top_isFiniteSolvableGaloisSubextension
example (E : IntermediateField S2847F6 S2847F6)
    (hE : isFiniteSolvableGaloisSubextension E) : E ≤ ⊤ :=
  maximalSolvableContains_top hE