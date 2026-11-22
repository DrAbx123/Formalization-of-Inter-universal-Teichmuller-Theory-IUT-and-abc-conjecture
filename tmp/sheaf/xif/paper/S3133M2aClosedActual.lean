import tmp.sheaf.xif.paper.S3137M2aToolActual
import tmp.sheaf.xif.paper.S3133M2aNormReductionActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# M2a CLOSED: actual canonical Gaussian q with norm 1/5 (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: lattice S3137 INDEX.R1.M2a,
mainline R1 registry/FINAL-STATUS, stage4/stepxi.

Source: IUT I, Example 3.2, (iv); IUT I, Definition 3.1, (b), (c); IUT III,
Definition 3.8, (i), p. 112-113.

The presentation bridge missing in the earlier parked attempt is Mathlib's
IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation':
  Valued.v ((k : K) : v.adicCompletion K) = v.valuation K k
for the Coe/global presentation (AdicValuation.lean:950).  With it, and lattice's
proved tools S3137M2aToolActual (rationalFivePlace_valuation_five,
norm_eq_absNorm_inv_of_valued_exp_neg_one, rationalFivePlace_asIdeal_eq_span)
plus the actual absNorm = 5 (Example36.concreteFiveHeightOne_asIdeal_eq_span +
gaussianRationalFive_absNorm), M2a is closed:

* S3133RationalFiveQCompletion: the actual rational scalar 5 in the contracted
  rational completion (Coe presentation);
* valuation = WithZero.exp (-1), nonzero;
* norm = 5^-1 via the canonical norm formula norm_eq_absNorm_zpow;
* S3133RationalFiveCompletionNorm_holds and
  S3133GaussianCanonicalQNorm_holds (via the proved reduction
  S3133GaussianCanonicalQNorm_of_rationalCompletionNorm and the actual isometry
  concretePlace_norm_completionMap_eq).
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped WithZero Valued BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133M2aClosedActual

local instance s3133ClosedGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3137M2aToolActual
open LeanFormal.IUT.XiFPaper.S3133M2aNormReductionActual
open LeanFormal.IUT.XiFPaper.S3133GaussianM2MissingActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

/-- The rational place contracted from the Gaussian five place. -/
abbrev S3133LowerFivePlace : NumberField.FinitePlace ℚ :=
  NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace

/-- The actual rational scalar 5 in the contracted rational completion, with the
mathlib WithVal/completion-coe presentation so that
IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' applies
syntactically. -/
noncomputable def S3133RationalFiveQCompletion :
    S3133LowerFivePlace.maximalIdeal.adicCompletion ℚ :=
  ⟨((WithVal.equiv (S3133LowerFivePlace.maximalIdeal.valuation ℚ)).symm (5 : ℚ) :
    (S3133LowerFivePlace.maximalIdeal.valuation ℚ).Completion)⟩

/-- Its valuation is exp(-1) (the actual uniformizer of the contracted place). -/
theorem S3133RationalFiveQCompletion_valuation :
    (Valued.v S3133RationalFiveQCompletion : WithZero (Multiplicative Int)) =
      WithZero.exp (-1) :=
  (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    S3133LowerFivePlace.maximalIdeal (5 : ℚ)).trans
    S3137M2aToolActual.rationalFivePlace_valuation_five

/-- It is nonzero. -/
theorem S3133RationalFiveQCompletion_ne_zero :
    S3133RationalFiveQCompletion ≠ 0 := by
  intro h0
  have hne : (Valued.v S3133RationalFiveQCompletion :
      WithZero (Multiplicative Int)) ≠ 0 := by
    rw [S3133RationalFiveQCompletion_valuation]
    exact WithZero.exp_ne_zero
  exact hne (by rw [h0, map_zero])

/-- Its canonical norm is exactly 1/5. -/
theorem S3133RationalFiveQCompletion_norm :
    ‖S3133RationalFiveQCompletion‖ = ((5 : Real)⁻¹) := by
  have hbase := S3137M2aToolActual.norm_eq_absNorm_inv_of_valued_exp_neg_one
    S3133LowerFivePlace S3133RationalFiveQCompletion
    S3133RationalFiveQCompletion_ne_zero S3133RationalFiveQCompletion_valuation
  have habs : (Ideal.absNorm S3133LowerFivePlace.maximalIdeal.asIdeal : ℝ) = 5 := by
    rw [S3137M2aToolActual.rationalFivePlace_asIdeal_eq_span,
      gaussianRationalFive_absNorm]
    norm_num
  rw [hbase, habs]

/-- **M2a base computation PROVED**: the exact base rational-completion norm
data required by S3133RationalFiveCompletionNorm. -/
theorem S3133RationalFiveCompletionNorm_holds :
    S3133RationalFiveCompletionNorm :=
  ⟨S3133RationalFiveQCompletion, S3133RationalFiveQCompletion_ne_zero,
    S3133RationalFiveQCompletion_norm⟩

/-- **M2a CLOSED**: an actual element of the canonical Gaussian completion with
norm exactly 1/5. -/
theorem S3133GaussianCanonicalQNorm_holds : S3133GaussianCanonicalQNorm :=
  S3133GaussianCanonicalQNorm_of_rationalCompletionNorm
    S3133RationalFiveCompletionNorm_holds

end LeanFormal.IUT.XiFPaper.S3133M2aClosedActual
