import tmp.sheaf.n8.closure.O2PaperReadoutActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import Mathlib

/-!
# O2 paper comparison: conditional actual closure

Using the exact residue-power theorem and the paper-qualified source fields:

1. W.q.order = 1 (the Tate parameter is a uniformizer);
2. LogShellResiduePowerCardHypothesis 1 (the log-shell index is the residue
   cardinal);
3. the residue-cardinality base agreement
   logShellResidueCard = residueNormBase at the selected F-place.

we prove ThetaAnab = ThetaQ.  Condition 3 is the exact missing production link
between the log-shell residue cardinal and the q normalization base; it is
carried as a source field, not chosen arbitrarily.

No arbitrary q, place, or readout is introduced.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open ABCBridge.N8.O2PaperComparison
open ABCBridge.N8.O2PaperReadoutActual

namespace ABCBridge.N8.O2PaperComparisonConditionalActual

universe u

variable {l : PrimeGeFive}

variable {D : SourceInitialThetaData l} (W : PaperBadFPlace D)

/-- The actual F-completion at the selected bad F-place. -/
abbrev FCompletion : Type :=
  CommonPrimeCompletion (K := D.candidate.arithmetic.F) ⟨W.place, rfl⟩

/-- Paper-qualified source conditions for the O2 comparison. -/
structure O2PaperSourceConditions : Prop where
  /-- The Tate parameter is a uniformizer. -/
  order_eq_one : W.q.order = 1
  /-- The log-shell index is the actual residue cardinal. -/
  residuePowerCard :
    LogShellResiduePowerCardHypothesis (K := FCompletion W) (p := W.prime) 1
  /-- The residue cardinal agrees with the q normalization base. -/
  residueCard_eq_base :
    (logShellResidueCard (K := FCompletion W) : ℝ) = residueNormBase W.place

/-- ThetaAnab is the logarithm of the actual residue cardinal under the
residue-power card hypothesis. -/
theorem thetaAnab_eq_log_residueCard
    (hcard : LogShellResiduePowerCardHypothesis
      (K := FCompletion W) (p := W.prime) 1) :
    PaperThetaAnab W = Real.log (logShellResidueCard (K := FCompletion W)) := by
  letI : Fact (Nat.Prime W.prime) :=
    ⟨(completionRationalPrime W.place).2⟩
  unfold PaperThetaAnab
  have h := logShellVolume_exact_residue_power
    (K := FCompletion W) (p := W.prime) hcard
  rw [h, pow_one]

/-- Under the paper-qualified source conditions, ThetaAnab = ThetaQ. -/
theorem thetaAnab_eq_thetaQ_of_sourceConditions
    (h : O2PaperSourceConditions W) :
    PaperThetaAnab W = PaperThetaQ W := by
  have hAnab := thetaAnab_eq_log_residueCard W h.residuePowerCard
  have hnorm : NormalizedThetaQ W = Real.log (residueNormBase W.place) := by
    unfold NormalizedThetaQ
    rw [h.order_eq_one]
    norm_num
  have hlogbase : Real.log (logShellResidueCard (K := FCompletion W)) =
      Real.log (residueNormBase W.place) :=
    congrArg Real.log h.residueCard_eq_base
  calc PaperThetaAnab W
      = Real.log (logShellResidueCard (K := FCompletion W)) := hAnab
    _ = Real.log (residueNormBase W.place) := hlogbase
    _ = NormalizedThetaQ W := hnorm.symm
    _ = PaperThetaQ W := normalizedThetaQ_eq_thetaQ W

/-- Conditional actual O2 paper comparison. -/
theorem o2PaperComparison_of_sourceConditions
    (h : O2PaperSourceConditions W) :
    O2PaperComparison W :=
  (thetaAnab_eq_thetaQ_of_sourceConditions W h).symm

end ABCBridge.N8.O2PaperComparisonConditionalActual
