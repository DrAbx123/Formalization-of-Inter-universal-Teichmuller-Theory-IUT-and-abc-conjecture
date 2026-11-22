/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RootImageRadiusFormulaActual
import Mathlib.Tactic

/-! # A766 hull: radius/coefficient dictionary bridge (arithmetic layer)

Green facts:
* hull A762: `log rootImageRadius_b = -(c_norm_b * log p_b)/(2l)` (radius coefficient
  `-1/(2l)` relative to `log p`; the max is at label j=1);
* lana (`Iut/WallEquiv/VcI.lean`):
  - `logShellRadius w p = sSup ((fun z => -ordp K w z) '' (logShell ... \ {0}))` (line 464);
  - tame hull per label: `∑_j (1 - 1/ramIdx_j) * log p`
    (`componentVol_leastHull_tensorLogShell_eq_tame`, line 435);
  - `logVol(vcI) = (Σ_i Σ^f hullPacket_i)/nC` (`logVol_hull_vcI_eq`, line 741).

The lana label contribution has exponent `j² - 1` (`j²` from theta `root^{j²}`, `-1` from
the log-shell unit part), so the label average is `sFactor(nC) - 1`; this file proves
the *arithmetic* identities and records the final bridge as an explicit inequality
parameter (no lana import is available yet in the vendor build). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1RadiusDictionaryBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual
open scoped BigOperators

/-- lana's `sFactor n = (Σ_{j<n} (j+1)^2)/n`. -/
noncomputable def sFactorArith (n : ℕ) : Real :=
  (∑ j : Fin n, (((j.1 : Real) + 1) ^ 2)) / (n : Real)

/-- lana's tame log-shell radius of a label: `ρ = 1 - 1/e`. -/
def lanaLogShellRadius (e : Real) : Real := 1 - e⁻¹

/-- The theta-side per-label log magnitude `j² * c_norm * log p / (2l)`. -/
def ourLabelLog (j : ℕ) (cNorm logp l : Real) : Real :=
  ((j : Real) ^ 2) * (cNorm * logp) / (2 * l)

/-- The lana per-label exponent `j² - 1` contribution. -/
def lanaLabelLog (j : ℕ) (cNorm logp l : Real) : Real :=
  (((j : Real) ^ 2) - 1) * (cNorm * logp) / (2 * l)

/-- Sum identity: `Σ_{j=1}^n (j² - 1) = n * (sFactor n - 1)`. -/
theorem sum_sq_sub_one (n : ℕ) (hn : 0 < n) :
    (∑ j : Fin n, ((((j.1 : Real) + 1) ^ 2) - 1)) =
      (n : Real) * (sFactorArith n - 1) := by
  unfold sFactorArith
  have hn' : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  field_simp

/-- Averaged identity: `(1/n) Σ_{j=1}^n (j² - 1) = sFactor n - 1`. -/
theorem average_sq_sub_one (n : ℕ) (hn : 0 < n) :
    (1 / (n : Real)) *
        (∑ j : Fin n, ((((j.1 : Real) + 1) ^ 2) - 1)) =
      sFactorArith n - 1 := by
  rw [sum_sq_sub_one n hn]
  field_simp [show (n : Real) ≠ 0 by exact_mod_cast hn.ne']

/-- The lana coefficient `(sFactor(nC) - 1)/(2l)`. -/
noncomputable def lanaCoefficient (nC : ℕ) (l : Real) : Real :=
  (sFactorArith nC - 1) / (2 * l)

/-- Hull's radius coefficient: `-1/(2l)` (`j = 1` radius). -/
noncomputable def radiusCoefficient (l : Real) : Real := -1 / (2 * l)

/-- `rootImageRadius` log coefficient form (A762 re-export), with coefficient `radiusCoefficient`. -/
theorem log_rootImageRadius_eq_radiusCoefficient
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) :
    Real.log (rootImageRadius T b : Real) =
      radiusCoefficient (l.value : Real) * (qVFamNormalizedCoefficient T b *
        Real.log (qVFamTensorP T b : Real)) := by
  rw [log_rootImageRadius_eq_neg_coeff_mul_logp_div_twoL]
  unfold radiusCoefficient
  ring

/-- **Final bridge (explicit parameter)**: if the lana hull log is at least our hull log,
then the SSIneq conclusion follows from the geometric chain and `c = (s-1)/(2l) <= 1`. -/
theorem ssiIneq_of_geometric_of_bridge {c absQ ourHull lanaHull : Real}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (habs : 0 ≤ absQ) (hgeom : absQ ≤ ourHull)
    (hbridge : ourHull ≤ lanaHull) : c * absQ ≤ lanaHull := by
  calc
    c * absQ ≤ 1 * absQ := mul_le_mul_of_nonneg_right hc1 habs
    _ = absQ := one_mul absQ
    _ ≤ ourHull := hgeom
    _ ≤ lanaHull := hbridge

/-- Numerical instance: at `l = 13`, `c_lana = 85/156`. -/
theorem coeff_l13 : (sFactorArith 6 - 1) / (2 * 13) = 85 / 156 := by
  unfold sFactorArith
  norm_num [Fin.sum_univ_six]

def bridgeRows : List (String × String × String) :=
  [ ("our radius", "rootImageRadius_b = p_b^(-c_norm/(2l)); log = -(c_norm log p)/(2l)", "A762 / S709 (GREEN)"),
    ("lana shell radius", "logShellRadius w p = sSup(-ordp z | z in logShell, z != 0)", "VcI.lean:464 (READ)"),
    ("lana tame label", "componentVol leastHull = sum_j (1 - 1/ramIdx_j) log p", "VcI.lean:435 (READ)"),
    ("lana label exponent", "j² - 1: j² from theta root^(j²), -1 from log-shell unit (2p)^-1 padicLog(1+pO)", "abc A765"),
    ("average identity", "(1/nC) sum_j (j² - 1) = sFactor(nC) - 1", "PROVED (average_sq_sub_one)"),
    ("lana coefficient", "c_lana = (sFactor(nC) - 1)/(2l)", "DEF + coeff_l13 = 85/156"),
    ("final bridge", "ourHullLog <= lanaHullLog (explicit hypothesis) => c_lana*absQ <= lanaHull", "PROVED conditional (ssiIneq_of_geometric_of_bridge)"),
    ("unproved bridge", "inequality ourHullLog <= lanaHullLog (or reverse) with archimedean nC*log(sqrt2*pi), 1/nC average, unit normalization terms", "EXPLICIT PARAMETER (not fabricated)") ]

theorem bridgeRows_length : bridgeRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1RadiusDictionaryBridgeActual.average_sq_sub_one
#print axioms LeanFormal.IUT.XiFPaper.Mzk1RadiusDictionaryBridgeActual.ssiIneq_of_geometric_of_bridge

end LeanFormal.IUT.XiFPaper.Mzk1RadiusDictionaryBridgeActual

end