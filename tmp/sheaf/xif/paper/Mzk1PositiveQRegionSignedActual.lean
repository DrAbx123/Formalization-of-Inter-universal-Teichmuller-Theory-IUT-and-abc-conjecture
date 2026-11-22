/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureQRegionActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import Mathlib.Tactic

/-!
# Mzk1PositiveQRegionSignedActual — signed Cor 3.12 from the positive-measure q region

A551: with the positive-measure q region (`PositiveQRegionRealization`) the strict
measure is a THEOREM from the Haar data, not a named field.  This file takes the
realization and derives the signed comparison `log vol(qRegion) ≤ log vol(hull)`
(from `Real.log_le_log` and `strict_measure`), then assembles the `StepXIContract`
and `Cor312Conclusion`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PositiveQRegionSignedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The signed q-pilot reading from the positive-measure realization:
`log vol(qRegion)`. -/
noncomputable def positiveSignedQ (R : PositiveQRegionRealization T) : Real :=
  Real.log (R.vol (positiveQRegion T))

/-- The signed Theta-pilot reading from the positive-measure realization:
`log vol(hull)`. -/
noncomputable def positiveSignedTheta (R : PositiveQRegionRealization T) : Real :=
  Real.log (R.vol (s1902Hull T))

/-- q-side positivity as a theorem from the realization's `q_pos`. -/
theorem positiveSignedQ_vol_pos (R : PositiveQRegionRealization T) :
    0 < R.vol (positiveQRegion T) := R.q_pos

/-- **Strict signed inequality as a theorem** (no named strict_measure):
`log vol(qRegion) < log vol(hull)` from `R.strict_measure` and `R.q_pos`. -/
theorem positiveSigned_strict (R : PositiveQRegionRealization T) :
    positiveSignedQ T R < positiveSignedTheta T R := by
  unfold positiveSignedQ positiveSignedTheta
  exact Real.log_lt_log R.q_pos R.strict_measure

/-- **Non-strict signed comparison as a theorem**. -/
theorem positiveSigned_le (R : PositiveQRegionRealization T) :
    positiveSignedQ T R ≤ positiveSignedTheta T R :=
  le_of_lt (positiveSigned_strict T R)

/-- The positive-measure realization contract: signed logs as q/theta slots,
target = theta (paper shape), qualitative slots explicit. -/
noncomputable def positiveContract (R : PositiveQRegionRealization T)
    (hqneg : positiveSignedQ T R < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) : StepXIContract :=
  signedCor312Contract (positiveSignedQ T R) (positiveSignedTheta T R) hqneg
    ipl hipl she hshe apt hapt (positiveSigned_le T R)

/-- Cor 3.12 conclusion from the positive-measure realization (strict_measure no
longer named: it is a theorem of the realization). -/
theorem positiveContract_cor312 (R : PositiveQRegionRealization T)
    (hqneg : positiveSignedQ T R < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (positiveContract T R hqneg ipl hipl she hshe apt hapt) :=
  signedCor312_conclusion (positiveSignedQ T R) (positiveSignedTheta T R) hqneg
    ipl hipl she hshe apt hapt (positiveSigned_le T R)

#check positiveSigned_strict
#check positiveContract_cor312

end LeanFormal.IUT.XiFPaper.Mzk1PositiveQRegionSignedActual
end
