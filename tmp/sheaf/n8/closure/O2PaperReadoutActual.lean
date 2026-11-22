import tmp.sheaf.n8.closure.O2PaperComparison
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib

/-!
# O2 paper readout: normalization and explicit exponent counterexample

ThetaQ = -log ||q|| for the actual ClauseB FinitePlaceQCandidate q.
ThetaAnab = log(logShellVolumeConsumer.index).

Using the actual exponent/order formulas:

  ThetaQ = order * log(residueNormBase place),

so the normalized ThetaQ by log(residueNormBase) is exactly the positive
discrete order.  The normalized O2 comparison is therefore exactly

  ThetaAnab = order * log(residueNormBase).

The q candidate is not arbitrary: ThetaAnab depends only on the selected
F-place, while replacing q by its positive power q^n multiplies ThetaQ by n
(the explicit different-uniformizer-exponent counterexample).  No arbitrary q
is introduced.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open ABCBridge.N8.O2PaperComparison

namespace ABCBridge.N8.O2PaperReadoutActual

universe u

variable {l : PrimeGeFive}

variable {D : SourceInitialThetaData l} (W : PaperBadFPlace D)

/-- Normalized paper ThetaQ: the q order times the local residue logarithm. -/
noncomputable def NormalizedThetaQ : ℝ :=
  (W.q.order : ℝ) * Real.log (residueNormBase W.place)

/-- The normalized ThetaQ is the actual ThetaQ. -/
theorem normalizedThetaQ_eq_thetaQ :
    NormalizedThetaQ W = PaperThetaQ W := by
  unfold NormalizedThetaQ
  change (W.q.order : ℝ) * Real.log (residueNormBase W.place) =
    localLogMagnitude W.q
  rw [localLogMagnitude_eq_order_mul_log]

/-- ThetaAnab is nonnegative: the actual log-shell volume index is positive. -/
theorem PaperThetaAnab_nonneg : 0 ≤ PaperThetaAnab W := by
  unfold PaperThetaAnab
  apply Real.log_nonneg
  have hpos : 0 < (logShellVolumeConsumer (K := CommonPrimeCompletion
    (K := D.candidate.arithmetic.F) ⟨W.place, rfl⟩)
    (p := W.prime)).index :=
    (logShellVolumeConsumer (K := CommonPrimeCompletion
      (K := D.candidate.arithmetic.F) ⟨W.place, rfl⟩)
      (p := W.prime)).index_pos
  have hle : 1 ≤ (logShellVolumeConsumer (K := CommonPrimeCompletion
    (K := D.candidate.arithmetic.F) ⟨W.place, rfl⟩)
    (p := W.prime)).index := Nat.succ_le_of_lt hpos
  exact_mod_cast hle

/-- Exact normalized O2 comparison: ThetaAnab equals the normalized ThetaQ. -/
theorem o2PaperComparison_iff_thetaAnab_eq_normalized :
    O2PaperComparison W ↔ PaperThetaAnab W = NormalizedThetaQ W := by
  rw [O2PaperComparison, normalizedThetaQ_eq_thetaQ]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Actual positive power candidate of the ClauseB q at the same F-place. -/
noncomputable def powTwoCandidate : FinitePlaceQCandidate W.place :=
  (W.q).pow 2 (by norm_num)

/-- TheThetaQ of the squared candidate is twice the original ThetaQ. -/
theorem thetaQ_powTwoCandidate :
    localLogMagnitude (powTwoCandidate W) = 2 * PaperThetaQ W := by
  unfold powTwoCandidate
  rw [localLogMagnitude_pow]
  change 2 * localLogMagnitude W.q = 2 * PaperThetaQ W
  congr 1

/-- Explicit different-exponent counterexample: at most one of q and q^2 can
satisfy the paper comparison with the same ThetaAnab. -/
theorem not_both_q_and_powTwo_compare
    (h1 : PaperThetaQ W = PaperThetaAnab W) :
    localLogMagnitude (powTwoCandidate W) ≠ PaperThetaAnab W := by
  intro h2
  have hpow : localLogMagnitude (powTwoCandidate W) = 2 * PaperThetaQ W :=
    thetaQ_powTwoCandidate W
  have hpos : 0 < PaperThetaQ W := PaperThetaQ_pos W
  linarith

/-- The exact O2 paper normalization gap: the comparison is exactly the
normalized readout identity; the arbitrary exponent q^n changes ThetaQ while
leaving ThetaAnab fixed, so a canonical paper ThetaQ needs the normalization /
exponent fixed. -/
def O2PaperNormalizationGap : Prop :=
  PaperThetaAnab W = NormalizedThetaQ W

end ABCBridge.N8.O2PaperReadoutActual
