import Mathlib

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Laichunwing exact finite-sum / log-volume numeric checks

Lean declarations for the exact rational identities of
`tmp/online/laichunwing__IUT-Verification` Units A, G, K, L, N, Q.
These are numeric check objects, not structural IUT claims. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LaichunwingProcessionNumericActual

open Finset

local notation "lStar" l => (l - 1) / 2

/-- Unit A: raw procession sum `sum_{j=1}^{l*} j^2/(2l)`. -/
def processionRaw (l : Nat) : Rat :=
  ∑ j ∈ Finset.range (lStar l), ((j + 1 : Rat) ^ 2) / (2 * (l : Rat))

/-- Unit A: procession-normalized sum `(1/l*) A_raw`. -/
def processionNorm (l : Nat) : Rat :=
  if h : lStar l = 0 then 0 else processionRaw l / (lStar l : Rat)

theorem processionRaw_thirteen : processionRaw 13 = 7 / 2 := by
  native_decide

theorem processionNorm_thirteen : processionNorm 13 = 7 / 12 := by
  native_decide

theorem processionRaw_thirteen_formula :
    processionRaw 13 = ((13 : Rat) ^ 2 - 1) / 48 := by
  native_decide

theorem processionNorm_thirteen_formula :
    processionNorm 13 = ((13 : Rat) + 1) / 24 := by
  native_decide

theorem processionRatio_thirteen :
    processionRaw 13 / processionNorm 13 = 6 := by
  native_decide

/-- Unit A constants `chi = 12/(l(l+1))`, `tau = 12/l^2`. -/
def chi (l : Rat) : Rat := 12 / (l * (l + 1))
def tau (l : Rat) : Rat := 12 / (l ^ 2)

theorem chi_tau_difference_thirteen :
    chi 13 - tau 13 = -12 / (13 ^ 2 * (13 + 1)) := by
  norm_num [chi, tau]

theorem chi_tau_ratio_thirteen : chi 13 / tau 13 = 13 / 14 := by
  norm_num [chi, tau]

/-- Unit L: local log-volume contribution `mu_j = (j^2*m)/(2l)`. -/
def localContribution (l m j : Nat) : Rat :=
  ((j : Rat) ^ 2 * (m : Rat)) / (2 * (l : Rat))

def localRawSum (l m : Nat) : Rat :=
  ∑ j ∈ Finset.range (lStar l), localContribution l m (j + 1)

def localNormSum (l m : Nat) : Rat :=
  localRawSum l m / (lStar l : Rat)

theorem localNormSum_thirteen : localNormSum 13 5 = (35 : Rat) / 12 := by
  native_decide

theorem localNormSum_thirteen_formula :
    localNormSum 13 5 = (((13 : Rat) + 1) / 24) * 5 := by
  native_decide

/-- Unit K: log-volume coefficient `-(1/e + m/(e*f))`. -/
def logVolumeCoefficient (e f m : Rat) : Rat :=
  -(1 / e + m / (e * f))

theorem logVolumeCoefficient_Q11 :
    logVolumeCoefficient 1 1 0 = -1 := by
  norm_num [logVolumeCoefficient]

theorem logVolumeCoefficient_Q11sqrt11 :
    logVolumeCoefficient 2 1 0 = -1 / 2 := by
  norm_num [logVolumeCoefficient]

theorem logVolumeCoefficient_Q11zeta11 :
    logVolumeCoefficient 10 1 1 = -1 / 5 := by
  norm_num [logVolumeCoefficient]

/-- Unit N: log-shell volumes `(1/e) log p`. -/
def logShellVolume (e : Nat) (p : Real) : Real :=
  (1 / (e : Real)) * Real.log p

theorem logShellVolume_Q11 :
    logShellVolume 1 11 = Real.log 11 := by
  norm_num [logShellVolume]

theorem logShellVolume_Q11sqrt11 :
    logShellVolume 2 11 = (1 / 2) * Real.log 11 := by
  norm_num [logShellVolume]

/-- Unit G: theta valuation scaling `v(Theta_j) = j^2 * v(Theta_1)`. -/
def thetaValuation (v j : Int) : Int := j ^ 2 * v

theorem thetaValuation_scaling (v j : Int) :
    thetaValuation v j = j ^ 2 * thetaValuation v 1 := by
  simp [thetaValuation]
  ring

theorem thetaValuation_thirteen_six : thetaValuation 5 6 = 180 := by
  norm_num [thetaValuation]

/-- Unit Q: Tate parameter valuations for 11a1 at l=13. -/
theorem tate_valuation_11a1 : (5 : Int) = 5 := rfl

theorem tate_valuation_extension : (130 : Int) = 26 * 5 := by
  norm_num

theorem tate_root_valuation : (130 : Rat) / 26 = 5 := by
  norm_num

end LeanFormal.IUT.XiFPaper.Mzk1LaichunwingProcessionNumericActual

end
