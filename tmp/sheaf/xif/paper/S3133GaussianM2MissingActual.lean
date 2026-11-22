import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.xif.paper.S3133GaussianCompletionTransportActual
import tmp.sheaf.xif.paper.S3133M2BaseQReductionActual
import tmp.sheaf.xif.paper.S3133GaussianBaseQActual

/-!
# M2 minimal exact missing: canonical completion q norm + clause-B descent (component)

COMPONENT, not a paper object.  Named consumers: task-57, lattice R1, mainline M2.

Source: IUT I, Example 3.2, (iv) (q_v parameters); IUT I, Definition 3.1, (b),
(c) (bad-place selection, residue characteristic p_v = 5); IUT II, Remark 2.5.1,
(i); IUT III, Definition 3.8, (i), p. 112-113; IUT III, Remark 3.1.1, (ii)-(iv),
p. 95-97.

STATUS of the last M2 pieces (task-57):

(a) transport Q_5 -> Gaussian Fmod completion: the actual transport into the
NORMALIZED completion is constructed and norm-preserving
(S3133GaussianCompletionTransportActual); the actual rational-side value 1/5 is
constructed (S3133GaussianBaseQActual).  The CANONICAL completion q norm value
(needed because FinitePlaceQCandidate lives in the canonical completion) reduces
to the canonical-versus-normalized completion norm comparison at the Gaussian
place — the same missing class as
Example36CompletionNormFormulaActual.NormalizedLogNormComparison.  This is the
exact missing S3133GaussianCanonicalQNorm below (page refs above).

(b) clause-B/Tate q descent (D4): the clause-B q is the actual qVFamily at the
lifted F-place (PROVED, S3133M2_clauseB_q_parameter); its identification with the
base q is the exact missing S3133GaussianClauseBDescent below.

PROVED reduction: if a canonical-completion element q with norm 1/5 exists and
the clause-B q at every bad place above 5 has the same norm as q, then M2 shrunk
(S3133GaussianQParameterMatchAtBase) holds with actual data.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133GaussianM2MissingActual

local instance s3133GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩


open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelMapMinimalActual
open LeanFormal.IUT.XiFPaper.S3133M2BaseQReductionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Exact missing M2(a): an actual element of the CANONICAL Gaussian completion
with norm exactly 1/5 (the canonical-versus-normalized completion norm
comparison at the Gaussian place). -/
def S3133GaussianCanonicalQNorm : Prop :=
  ∃ q : Completion concreteGaussianFivePlace,
    q ≠ 0 ∧ ‖q‖ = ((5 : Real)⁻¹)

/-- Exact missing M2(b): clause-B/Tate q descent (D4): at every bad place above
5 the clause-B q has the same canonical norm as the Gaussian base q. -/
def S3133GaussianClauseBDescent : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    (completionRationalPrime (nativeBadToFPlace T b)).val = 5 →
      ∀ q : Completion concreteGaussianFivePlace, ‖q‖ = ((5 : Real)⁻¹) →
        ‖(qVFamily T b).q‖ = ((5 : Real)⁻¹)

/-- PROVED reduction: an actual canonical-completion q of norm 1/5 together
with the clause-B descent gives the shrunk M2 Gaussian q-parameter match. -/
theorem S3133GaussianQParameterMatchAtBase_of_canonicalQ
    (q : Completion concreteGaussianFivePlace)
    (hq : ‖q‖ = ((5 : Real)⁻¹))
    (hlink : ∀ b : Bad (nativePlaceSelection T),
      (completionRationalPrime (nativeBadToFPlace T b)).val = 5 →
        ‖(qVFamily T b).q‖ = ‖q‖) :
    S3133GaussianQParameterMatchAtBase T := by
  intro b h5
  rw [hlink b h5, hq]

end LeanFormal.IUT.XiFPaper.S3133GaussianM2MissingActual
