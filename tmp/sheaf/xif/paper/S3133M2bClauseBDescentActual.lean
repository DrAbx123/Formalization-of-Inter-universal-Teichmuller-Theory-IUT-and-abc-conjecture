import tmp.sheaf.xif.paper.S3133GaussianM2MissingActual
import tmp.sheaf.xif.paper.S3133M2aNormReductionActual
import tmp.sheaf.xif.paper.S3133S3131GaussianModelMapMinimalActual

/-!
# M2b linkage: clause-B descent versus the shrunk Gaussian q-parameter match

COMPONENT, not a paper object.  Named consumers: task-60 M2b, lattice R1,
mainline M2.

Source: IUT I, Definition 3.1, (b), (c); IUT I, Example 3.2, (iv); IUT II,
Remark 2.5.1, (i); IUT III, Definition 3.8, (i), p. 112-113.

The exact missing M2b (S3133GaussianClauseBDescent) is equivalent to the shrunk
Gaussian q-parameter match given the M2a canonical q.  Both directions are
proved here.  The generic SourceClauseB structure (SourceDefinition31Quantifiers)
only supplies an arbitrary FinitePlaceQCandidate witness at each bad F-place and
a Tate curve comparison; it carries NO norm value, so the value 1/5 is the
paper's chosen q_v (D4, IUT I Definition 3.1(b), Example 3.2(iv)) and cannot be
derived from the generic clause structure alone.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133M2bClauseBDescentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3133M2BaseQReductionActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelMapMinimalActual
open LeanFormal.IUT.XiFPaper.S3133GaussianM2MissingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- If the shrunk Gaussian q-parameter match holds, the M2b clause-B descent
holds (the descent only re-states the per-bad-place norm). -/
theorem S3133GaussianClauseBDescent_of_atBase
    (h : S3133GaussianQParameterMatchAtBase T) :
    S3133GaussianClauseBDescent T := by
  intro b h5 q hq
  exact h b h5

/-- The M2b clause-B descent plus the M2a canonical q gives the shrunk Gaussian
q-parameter match: the two remaining M2 exact missing pieces are jointly exactly
the shrunk model match. -/
theorem S3133GaussianQParameterMatchAtBase_of_ClauseBDescent_and_canonicalQ
    (hq : S3133GaussianCanonicalQNorm)
    (h : S3133GaussianClauseBDescent T) :
    S3133GaussianQParameterMatchAtBase T := by
  obtain ⟨q, _hqne, hqnorm⟩ := hq
  intro b h5
  exact h b h5 q hqnorm

end LeanFormal.IUT.XiFPaper.S3133M2bClauseBDescentActual
