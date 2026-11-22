import tmp.sheaf.xif.paper.S3133GaussianM2MissingActual
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

/-!
# M2a reduction: canonical Gaussian q norm from the rational-completion base norm

COMPONENT, not a paper object.  Named consumers: task-60 M2a, lattice R1,
mainline normalization area.

Source: IUT I, Example 3.2, (iv); IUT I, Definition 3.1, (b), (c); IUT III,
Definition 3.8, (i), p. 112-113.

M2a (S3133GaussianCanonicalQNorm: actual canonical-completion q with norm 1/5)
REDUCED to the concrete rational base-field completion norm
S3133RationalFiveCompletionNorm.  The reduction is proved with the actual norm
transport norm_completionMap_pow at the Gaussian place and the proved relative
completion degree one (concreteGaussianFivePlace_relativeCompletionDegree_eq_one):
the canonical completion norm of the image of the base 5 equals the base
canonical norm to the power 1.  Remaining exact missing is therefore the
BASE-FIELD computation of the canonical norm of 5 in the completion of Q at the
rational five place (the same class as the normalized-log-norm comparison, but
here the base field is Q, where the canonical formula
norm_eq_absNorm_zpow is available; see ledger).
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133M2aNormReductionActual

local instance s3133GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S3133GaussianM2MissingActual

/-- The concrete rational base-field completion norm data for the scalar 5:
the exact base computation M2a reduces to (nonzero certificate plus canonical
norm value). -/
def S3133RationalFiveCompletionNorm : Prop :=
  ∃ x : (comap (k := ℚ) concreteGaussianFivePlace).maximalIdeal.adicCompletion ℚ,
    x ≠ 0 ∧ ‖x‖ = ((5 : Real)⁻¹)

/-- M2a REDUCED: the base rational-completion norm data gives an actual
canonical-completion Gaussian q with norm 1/5. -/
theorem S3133GaussianCanonicalQNorm_of_rationalCompletionNorm
    (h : S3133RationalFiveCompletionNorm) : S3133GaussianCanonicalQNorm := by
  obtain ⟨x, hx0⟩ := h
  obtain ⟨hx, hnorm⟩ := hx0
  unfold S3133GaussianCanonicalQNorm
  refine ⟨completionMap (k := ℚ) (K := GaussianField) concreteGaussianFivePlace x,
    ?_, ?_⟩
  · intro hzero
    exact hx (completionMap_injective (k := ℚ) concreteGaussianFivePlace
      (by simpa using hzero))
  · rw [norm_completionMap_pow (k := ℚ) (K := GaussianField)
      (place := concreteGaussianFivePlace) (x := x) hx]
    rw [concreteGaussianFivePlace_relativeCompletionDegree_eq_one, pow_one]
    simpa using hnorm

end LeanFormal.IUT.XiFPaper.S3133M2aNormReductionActual
