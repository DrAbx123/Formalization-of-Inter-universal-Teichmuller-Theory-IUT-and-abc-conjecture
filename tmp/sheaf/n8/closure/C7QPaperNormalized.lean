import tmp.sheaf.n8.closure.C7QPilotRegionActual
import tmp.sheaf.n8.closure.C7NormalizedDivisors

/-!
# C7 normalized paper q readout

qside qPilotMass is the normalized C6 mass of the actual q-scaled region.
The expected actual mass formula is qPilotMass = ||q||^d, where
d = finrank_Qp of the one-factor completion.  Hence
QPaper = log(qPilotMass) = d * log||q||, and the paper-normalized readout is

  QPaperNorm := QPaper / d.

This is not arbitrary: d is the actual Qp-dimension and QPaper is the actual
mass log.  The law with normalized C6 divisors is equivalent to
QPaperNorm = rNorm; the mass formula and this identification remain exact gaps.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.C7NormalizedDivisors
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped ENNReal

namespace LeanFormal.IUT.N8Closure.C7QPaperNormalized

/-- Actual Qp-dimension of the one-factor q-pilot completion. -/
noncomputable def dQ {l : PrimeGeFive} (S : SourceInitialThetaData l) : Nat :=
  Module.finrank ℚ_[pNat S] (CommonPrimeCompletion (placeAtPrime S))

/-- Actual mass-log readout from qside. -/
noncomputable def QPaper {l : PrimeGeFive} (S : SourceInitialThetaData l) : Real :=
  C7QPilotRegionActual.QPaper S

/-- Paper-normalized q readout: divide the mass log by the actual Qp-dimension. -/
noncomputable def QPaperNorm {l : PrimeGeFive} (S : SourceInitialThetaData l) : Real :=
  QPaper S / (dQ S : Real)

/-- Expected actual mass formula: qPilot mass = ||q||^d. -/
def QPaperMassFormula {l : PrimeGeFive} (S : SourceInitialThetaData l) : Prop :=
  qPilotMass S = ENNReal.ofReal (‖q S‖ ^ dQ S)

/-- Conditional consequence of the mass formula: normalized readout is
log||q||. -/
theorem QPaperNorm_eq_log_norm_of_mass {l : PrimeGeFive}
    (S : SourceInitialThetaData l) (h : QPaperMassFormula S)
    (hd : dQ S ≠ 0) (hq : q S ≠ 0) :
    QPaperNorm S = Real.log ‖q S‖ := by
  unfold QPaperNorm QPaper QPaperMassFormula at *
  unfold C7QPilotRegionActual.QPaper
  rw [h]
  rw [ENNReal.toReal_ofReal (pow_nonneg (norm_nonneg _) _)]
  rw [Real.log_pow]
  have hdR : (dQ S : Real) ≠ 0 := by exact_mod_cast hd
  field_simp [hdR]

/-- Normalized C6 paper law with A=rNorm, Z=hNorm. -/
def C7QPaperNormalizedLaw {l : PrimeGeFive} (S : SourceInitialThetaData l) : Prop :=
  hNorm S - QPaperNorm S = Z S - A S

/-- The normalized law is exactly QPaperNorm = rNorm. -/
theorem c7QPaperNormalizedLaw_iff {l : PrimeGeFive}
    (S : SourceInitialThetaData l) :
    C7QPaperNormalizedLaw S ↔ QPaperNorm S = rNorm S := by
  unfold C7QPaperNormalizedLaw Z A
  constructor <;> intro hh <;> linarith

/-- Exact remaining identification target. -/
def MissingQPaperNormalizedIdentification {l : PrimeGeFive}
    (S : SourceInitialThetaData l) : Prop := QPaperNorm S = rNorm S

end LeanFormal.IUT.N8Closure.C7QPaperNormalized
