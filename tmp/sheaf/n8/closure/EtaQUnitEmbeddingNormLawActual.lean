import tmp.sheaf.n8.closure.EtaQUnitAlgClDepthActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIntoAlgCl

set_option maxHeartbeats 1200000

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQUnitEmbeddingNormLawActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaQUnitAlgClDepthActual
open LeanFormal.IUT.N8Closure.EtaQActual
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaShellQUnitCandidateActual
open LeanFormal.IUT.N8Closure.EtaShellDepthScalingActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : NormedField (fPlaceShell X).K :=
  NumberFieldFinitePlace.commonPrimeCompletionNormedField
    (place := nativeFPlaceAtPrime X)

/-- Exact missing isometry theorem: the actual F-completion embedding into
PadicAlgCl preserves the norm on the whole completion. -/
def EtaCompletionEmbeddingIsometry : Prop :=
  ∀ x : EtaShellQUnitCandidateActual.QCompletion X,
    ‖fCompletionToPadicAlgCl X (x : (fPlaceShell X).K)‖ = ‖x‖

/-- Conditional norm law for the qUnit: follows immediately from the
actual completion isometry. -/
theorem qUnitEmbeddingNormLaw_of_isometry
    (h : EtaCompletionEmbeddingIsometry X) :
    EtaQUnitEmbeddingNormLaw X := by
  unfold EtaQUnitEmbeddingNormLaw
  have hq : ((qUnitAlgCl X : AlgClUnits X) : PadicAlgCl (nativePrime X)) =
      fCompletionToPadicAlgCl X (qUnitK X) := rfl
  rw [hq]
  simpa [qUnitK] using h (etaQUnit X)

/-- Conditional unconditional depth: under the actual completion isometry,
the qUnit AlgCl depth is `-qPilotSignedLog`. -/
theorem qUnitAlgCl_depth_of_isometry
    (h : EtaCompletionEmbeddingIsometry X) :
    unitShellDepth (nativePrime X) (qUnitAlgCl X) = -qPilotSignedLog X :=
  qUnitAlgCl_depth_of_normLaw X (qUnitEmbeddingNormLaw_of_isometry X h)

/-! ## Exact gap -/

/- The isometry is not in the production tree: `Example36CompletionIntoAlgCl`
records the valuation-normalization compatibility as missing and only proves
injectivity of the universal-property embedding.  The exact missing theorem
is the normalized-value/isometry equality above; no norm is asserted. -/
def EtaCompletionEmbeddingIsometryGap : Prop :=
  ¬ EtaCompletionEmbeddingIsometry X

def EtaQUnitEmbeddingNormLawGapActual : Prop :=
  ¬ EtaQUnitEmbeddingNormLaw X

end LeanFormal.IUT.N8Closure.EtaQUnitEmbeddingNormLawActual
