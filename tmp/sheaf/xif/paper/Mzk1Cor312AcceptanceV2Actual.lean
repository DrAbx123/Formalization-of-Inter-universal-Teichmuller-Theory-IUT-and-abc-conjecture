/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # A550 acceptance artifact: IUT III Corollary 3.12 final chain

## Green chain (olean state at acceptance)
* `Mzk1KummerTransportActual` (EXIT=0, olean 00:09 UTC): `kummerMap`, `thetaOneCarrier`,
  `qPilotInThetaCarrier`, `kummerMap_thetaOne` (SHE root relation `q = theta^(2l)`),
  `qPilotInThetaCarrier_mem_hull` (genuine containment from SHE + norm bounds),
  `KummerXiERealization` (vol/vol_mono/q_pos/strict_measure).
* `Mzk1KummerRealizationActual` (EXIT=0, olean 00:04 UTC): `qImage_realized`,
  `thetaImage_realized`, `qImage_realized_mem_hull`, `PaperKummerReading`,
  `paperKummerReading_strict`, `paperKummerReading_CTheta`.
* `Mzk1XiEContainmentRequirementActual` (EXIT=0, olean 23:34 UTC):
  `XiEContainmentRequirement` (q_in_possible / possible_in_hull / strict_measure),
  `requirement_strict_signed`, `requirement_signed_inequality`, `requirement_cor312`.
* `Mzk1Cor312FinalAssemblyActual` (EXIT=0, olean 00:14 UTC): `requirementOfReading`,
  `no_defeq_vacuity`, `target_matches_paper`, `cor312Contract_final`, `cor312Conclusion_final`,
  `genuine_logVolume_inequality_SHE`.

## Axiom gate (A548/A549, `Mzk1Cor312AxiomGateActual` watchdog log)
`#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.cor312Conclusion_final`
= `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no custom axioms; same for
`paperKummerReading_strict`, `genuine_logVolume_inequality`, `requirement_strict_signed`,
`genuine_logVolume_inequality_SHE`.

## Named inputs of the chain (THEOREM HYPOTHESES, not axioms)
* `R : PaperKummerReading T` — the paper 1-column readout equalities
  `qReading_log`/`thetaReading_log` of `-|log q|` / `-|log(Theta)|` with the realized
  log-volumes;
* `hqneg` — the signed q reading is negative (paper `|log q| > 0`);
* `strict_measure` — strict volume increase of the hull over the q image
  (non-vacuity witness of the xi-e requirement);
* `ipl`, `she`, `apt` — the real `(IPL)/(SHE)/(APT)` evidence Props supplied as
  arguments with proofs (never instantiated with `True` here).

## Paper statement (IUT III:10324-10353)
`-|log(Theta)| >= -|log q|`, equivalently `C_Theta >= -1` for every real `C_Theta` with
`-|log(Theta)| <= C_Theta * |log q|`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The assembled Cor 3.12 conclusion (explicit instance) -/

/-- **Cor 3.12 final conclusion** (explicit instance of the assembled chain): for every
  paper reading `R` with negative q reading and real `(IPL)/(SHE)/(APT)` evidence, the
  final StepXI contract satisfies `Cor312Conclusion` (i.e. `qSigned <= thetaSigned`). -/
theorem cor312_conclusion (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt) :=
  cor312Conclusion_final T R hqneg ipl hipl she hshe apt hapt

/-- The contract's q/Theta slots are the paper readings `-|log q|`, `-|log(Theta)|`. -/
theorem cor312_conclusion_slots (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt).qSigned =
        requirementSignedQ (requirementOfReading T R) ∧
      (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt).thetaSigned =
        requirementSignedTheta (requirementOfReading T R) := by
  constructor
  · rfl
  · rfl

/-! ## 2. Paper statement in signed form -/

/-- **`-|log(Theta)| >= -|log q|`** (signed paper form): the realized q reading is at
  most the realized Theta-hull reading. -/
theorem acceptance_paper_statement (R : PaperKummerReading T) :
    R.thetaReading ≥ R.qReading :=
  le_of_lt (paperKummerReading_strict T R)

/-- Strict version of the paper statement: `-|log(Theta)| > -|log q|`. -/
theorem acceptance_paper_statement_strict (R : PaperKummerReading T) :
    R.thetaReading > R.qReading :=
  paperKummerReading_strict T R

/-- The `C_Theta >= -1` form of the paper statement. -/
theorem acceptance_CTheta (R : PaperKummerReading T) (hqneg : R.qReading < 0)
    {C : ℝ} (hC : R.thetaReading ≤ C * (-R.qReading)) : -1 ≤ C := by
  have hqpos : 0 < -R.qReading := neg_pos.mpr hqneg
  have h1 : R.qReading < C * (-R.qReading) :=
    lt_of_lt_of_le (paperKummerReading_strict T R) hC
  have h2 : R.qReading / (-R.qReading) < C := (div_lt_iff₀ hqpos).mpr h1
  have hne : R.qReading ≠ 0 := ne_of_lt hqneg
  have h3 : R.qReading / (-R.qReading) = -1 := by
    calc R.qReading / (-R.qReading) = -(R.qReading / R.qReading) := by rw [div_neg]
      _ = -(1 : ℝ) := by rw [div_self hne]
      _ = -1 := by ring
  rw [h3] at h2
  linarith

end Mzk1Cor312AcceptanceV2Actual

