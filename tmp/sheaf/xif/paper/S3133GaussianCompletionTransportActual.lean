import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteFinitePlaceBoundary
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionNormFormulaActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

/-!
# Actual Gaussian-completion transport and norm preservation (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: task-57 M2, lattice R1,
mainline M2.

Source: IUT I, Example 3.2, (iv) (q_v parameters); IUT I, Definition 3.1, (b),
(c); IUT III, Definition 3.8, (i), p. 112-113.

PROVED here:
* the actual Gaussian base Fmod place lies above the rational prime 5
  (concreteGaussianFivePlace_comap + the actual rational-place construction);
* the actual p-adic scalar transport into the Gaussian completion exists as the
  actual homomorphism padicCompletionHom concreteGaussianFivePlace;
* the actual transport into the NORMALIZED completion preserves the q norm:
  normalizedCompletion_norm_algebraMap (proved in
  Example36CompletionNormFormulaActual) instantiated at the Gaussian place.

What remains exact missing (recorded in S3133GaussianM2MissingActual): the
CANONICAL completion q norm value 1/5, i.e. the canonical-versus-normalized
completion norm comparison at the Gaussian place (the same missing class as
Example36CompletionNormFormulaActual.NormalizedLogNormComparison), and the
clause-B/Tate q descent (D4).  These are pages IUT I Example 3.2(iv),
IUT I Definition 3.1(b)(c), IUT III Definition 3.8(i).
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133GaussianCompletionTransportActual

local instance s3133GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩


open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36

/-- The rational prime of the actual Gaussian base Fmod place is 5. -/
theorem S3133GaussianFivePlace_prime :
    (completionRationalPrime concreteGaussianFivePlace).val = 5 := by
  unfold completionRationalPrime
  rw [concreteGaussianFivePlace_comap]
  have hval : (Rat.HeightOneSpectrum.primesEquiv
      (R := NumberField.RingOfIntegers ℚ) concreteFiveHeightOne).val = 5 :=
    congrArg Subtype.val
      ((Rat.HeightOneSpectrum.primesEquiv
        (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply concreteFivePrime)
  simpa [concreteFivePlace_maximalIdeal] using hval

/-- The actual p-adic scalar field at the Gaussian base place is the rational
p-adic scalar field over 5 (type-level identification via the actual place). -/
abbrev S3133GaussianPadicScalar : Type :=
  PadicScalarField concreteGaussianFivePlace

/-- The actual rational p-adic transport into the Gaussian completion. -/
noncomputable def S3133GaussianPadicCompletionHom :
    S3133GaussianPadicScalar →+* Completion concreteGaussianFivePlace :=
  padicCompletionHom concreteGaussianFivePlace

/-- Norm preservation of the actual transport into the NORMALIZED Gaussian
completion (proved normalization theorem, instantiated at the Gaussian place). -/
theorem S3133GaussianNormalizedTransport_norm_preserving
    (a : S3133GaussianPadicScalar) :
    ‖(algebraMap S3133GaussianPadicScalar
        (NormalizedCompletion concreteGaussianFivePlace)) a‖ = ‖a‖ :=
  normalizedCompletion_norm_algebraMap concreteGaussianFivePlace a

end LeanFormal.IUT.XiFPaper.S3133GaussianCompletionTransportActual
