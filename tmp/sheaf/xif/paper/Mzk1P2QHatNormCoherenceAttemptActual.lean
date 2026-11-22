/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2QNativeReadingCorrectedActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import Mathlib.Tactic

/-! # P2: attempt at QHatNormCoherence (c0QHat norm = normalized norm)

Goal: `‖c0QHat T b‖ = qVFamNormalizedNorm T b`.  With `c0QHat_eq_q` this reduces to
`‖algebraMap (rootBase) L ((qVFamily q : rootBase))‖ = ‖qVFamNormalizedGenerator‖`.
`norm_algebraMap'` gives `‖algebraMap x‖ = ‖x‖` when the target has `NormOneClass`, so the
only remaining point is that `rootBase T b` and `CommonPrimeCompletion (qVFamTensorPlaces T b)()`
carry the **same norm instance**.  If this fails, the first error identifies the exact
norm-instance mismatch (no assumption). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2QHatNormCoherenceAttemptActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Attempt: the c0QHat norm equals the normalized norm (evidence: `norm_algebraMap'`). -/
theorem qHatNormCoherence_attempt :
    ‖c0QHat T b‖ = qVFamNormalizedNorm T b := by
  rw [c0QHat_eq_q]
  change ‖algebraMap (rootBase T b) (rootNormedExtension T b)
      (((qVFamily T b).q : rootBase T b))‖ = qVFamNormalizedNorm T b
  rw [norm_algebraMap']
  change ‖((qVFamily T b).q : rootBase T b)‖ =
    ‖((qVFamily T b).q : CommonPrimeCompletion ((qVFamTensorPlaces T b) () ()))‖
  rfl

def coherenceAttemptRows : List (String × String × String) :=
  [ ("qHatNormCoherence_attempt", "c0QHat norm = qVFamNormalizedNorm (attempt)", "ATTEMPT") ]

theorem coherenceAttemptRows_length : coherenceAttemptRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P2QHatNormCoherenceAttemptActual

end