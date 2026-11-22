/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2QNativeReadingCorrectedActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.S305SingleLambdaNormActual
import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import tmp.sheaf.xif.paper.O2QrootGlueActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import Mathlib.Tactic

/-! # P2: QHatNormCoherence proof via the S305 norm power identity

`c0QHat = c0Alpha^(2l)`, `c0Alpha = qrootElem = rootNormedElement` (in L), so
`‖c0QHat‖ = ‖rootNormedElement‖^(2l) = qVFamNormalizedNorm` by `norm_pow` + S305.
This closes `P2QHatNormInstanceAgreement` unconditionally (no `norm_algebraMap` needed). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2QHatNormCoherenceProofActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1P2QNativeReadingCorrectedActual
open LeanFormal.IUT.XiFPaper.S305SingleLambdaNormActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.O2QrootGlueActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The c0QHat norm equals the normalized norm (QHat norm-instance coherence). -/
theorem qHatNormCoherence_proved : ‖c0QHat T b‖ = qVFamNormalizedNorm T b := by
  rw [c0QHat, c0Alpha]
  rw [norm_pow]
  have h : ‖qrootElem T b‖ = rootNormedElementNorm T b := rfl
  rw [h]
  exact rootNormedElementNorm_pow_twoL_eq_qVFamNormalizedNorm (T := T) (b := b)

/-- `P2QHatNormInstanceAgreement` holds unconditionally. -/
theorem p2QHatNormInstanceAgreement_proved :
    P2QHatNormInstanceAgreement T :=
  fun b => qHatNormCoherence_proved T b

def qHatCoherenceProofRows : List (String × String × String) :=
  [ ("qHatNormCoherence_proved", "||c0QHat|| = qVFamNormalizedNorm via norm_pow + S305", "PROVED"),
    ("p2QHatNormInstanceAgreement_proved", "P2QHatNormInstanceAgreement unconditional", "PROVED") ]

theorem qHatCoherenceProofRows_length : qHatCoherenceProofRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P2QHatNormCoherenceProofActual

end