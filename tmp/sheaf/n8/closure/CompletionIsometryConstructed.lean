import tmp.sheaf.n8.closure.EtaQUnitEmbeddingNormLawActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIsometry

set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.N8Closure.CompletionIsometryConstructed

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaQUnitAlgClDepthActual
open LeanFormal.IUT.N8Closure.EtaQUnitEmbeddingNormLawActual
open LeanFormal.IUT.N8Closure.EtaQActual
open LeanFormal.IUT.N8Closure.EtaShellQUnitCandidateActual
open LeanFormal.IUT.N8Closure.EtaShellDepthScalingActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- The production normalized-completion norm on the F-shell carrier. -/
noncomputable def normalizedShellNorm (x : (fPlaceShell X).K) : ℝ :=
  @norm (fPlaceShell X).K
    (@NormedField.toNorm (fPlaceShell X).K
      (normalizedCompletionNontriviallyNormedField
        (nativeFPlaceOverBad X)).toNormedField) x

/-- Constructed actual isometry for the normalized completion norm: the
F-completion embedding into `PadicAlgCl` preserves it, by production
`normalizedCompletionEmbedding_isometry`. -/
theorem fCompletionToPadicAlgCl_isometry_normalized
    (x : (fPlaceShell X).K) :
    ‖fCompletionToPadicAlgCl X x‖ = normalizedShellNorm X x := by
  exact normalizedCompletionEmbedding_isometry
    (F := X.S.arithmetic.F) (place := nativeFPlaceOverBad X)
    (φ := fCompletionToPadicAlgCl X) x

/-! ## Exact canonical/normalized norm bridge -/

/-- The exact missing bridge: on the qUnit, the canonical completion norm
(used by qPilot/etaQScalar) equals the production normalized completion norm
(used by the spectral isometry). -/
def EtaCanonicalNormalizedNormBridge : Prop :=
  normalizedShellNorm X (qUnitK X) =
    ‖(etaQUnit X : EtaShellQUnitCandidateActual.QCompletion X)‖

/-- Conditional qUnit norm law from the canonical/normalized norm bridge. -/
theorem qUnitEmbeddingNormLaw_of_normBridge
    (hbridge : EtaCanonicalNormalizedNormBridge X) :
    EtaQUnitEmbeddingNormLaw X := by
  unfold EtaQUnitEmbeddingNormLaw
  have hq : ((qUnitAlgCl X : AlgClUnits X) : PadicAlgCl (nativePrime X)) =
      fCompletionToPadicAlgCl X (qUnitK X) := rfl
  rw [hq, fCompletionToPadicAlgCl_isometry_normalized]
  unfold EtaCanonicalNormalizedNormBridge at hbridge
  exact hbridge

theorem qUnitAlgCl_depth_of_normBridge
    (hbridge : EtaCanonicalNormalizedNormBridge X) :
    unitShellDepth (nativePrime X) (qUnitAlgCl X) = -qPilotSignedLog X :=
  qUnitAlgCl_depth_of_normLaw X (qUnitEmbeddingNormLaw_of_normBridge X hbridge)

def EtaCanonicalNormalizedNormBridgeGap : Prop :=
  ¬ EtaCanonicalNormalizedNormBridge X

end LeanFormal.IUT.N8Closure.CompletionIsometryConstructed
