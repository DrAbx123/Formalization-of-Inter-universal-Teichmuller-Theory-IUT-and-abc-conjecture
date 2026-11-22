/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1AxiomGateActual
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalActual
import tmp.sheaf.xif.paper.Mzk1PaperTargetMatchingActual
import tmp.sheaf.xif.paper.Mzk1FinalAssemblySelfChecksActual
import Mathlib.Tactic
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.n8.closure.SourcePilotRegion

/-!
# Mzk1AcceptanceFinalChecksActual — acceptance checks on green components (A553)

Machine-checked acceptance checks over the green final components:
* the final assembly's `Cor312Conclusion` payload (`axiomGate_cor312Conclusion_final`);
* the paper target match (`target_matches_paper`);
* the IUT IV Stage-5 reduction `abcConjecture_of_literalLogVolumeEstimates`;
* the self-check that the contract target is not the q slot (`target ≠ q`).

No new axiom, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AcceptanceFinalChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1AxiomGateActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperTargetMatchingActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblySelfChecksActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- Acceptance check 1: the paper target match holds (iff three components). -/
theorem acceptanceCheck_paperTargetMatch :
    PaperTargetStatement C3 P ↔
      ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ ∧
        qPilotLogVolumeReading P ≤ 0 ∧
        qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3) :=
  target_matches_paper C3 P

/-- Acceptance check 2: the paper target follows from the signed comparison. -/
theorem acceptanceCheck_paperTarget_of_comparison
    (h : qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3) :
    PaperTargetStatement C3 P :=
  paperTarget_of_comparison C3 P h

/-- Acceptance check 3: the IUT IV Stage-5 reduction is available. -/
theorem acceptanceCheck_abcStage5
    (logVolume : Nat → Nat → Nat → Real) (hullVolume : Real)
    (hheight : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : Real, 0 < δ → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    ABCConjecture :=
  abcConjecture_of_literalLogVolumeEstimates logVolume hullVolume hheight hmain

/-- Acceptance check 4: the assembled contract target is θ (not q). -/
theorem acceptanceCheck_target_identity (q theta : Real) (hqneg : q < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : q ≤ theta) :
    (LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual.signedCor312Contract
      q theta hqneg ipl hipl she hshe apt hapt hle).targetSigned = theta :=
  rfl

#check acceptanceCheck_paperTargetMatch
#check acceptanceCheck_abcStage5
#check acceptanceCheck_target_identity

end LeanFormal.IUT.XiFPaper.Mzk1AcceptanceFinalChecksActual
end
