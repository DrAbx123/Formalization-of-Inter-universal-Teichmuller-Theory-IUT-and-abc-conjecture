import tmp.sheaf.xif.paper.S1298TorsionClauseActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace ProbeS1351

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual

local instance probeGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

def fibreQuadratic {K : Type*} [CommRing K] (W : WeierstrassCurve K) (x : K) : K[X] :=
  X ^ 2 + C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))

section Fibre
variable {K : Type*} [Field K] [DecidableEq K]

theorem fibreQuadratic_eval_iff (W : WeierstrassCurve.Affine K) (x y : K) :
    (fibreQuadratic W x).eval y = 0 ↔ W.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff']
  simp only [fibreQuadratic, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  constructor <;> intro h
  · ring_nf at h ⊢
  · ring_nf at h ⊢

end Fibre

end ProbeS1351
