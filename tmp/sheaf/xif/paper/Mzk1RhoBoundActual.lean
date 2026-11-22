/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A827 hull: per-place facts for the volume upper chain

Three per-place facts:
1. `rho_w <= b_w + 1 + [p=2]`;
2. `d_w + a_w >= 1 + [p=2]`;
3. `-x <= -floor(x)`.

Green assets:
* `IntegralLogShellSharpBounds.logShellPaperAExponent` (`1/e * ceil(e/(p-2))`, `2` at p=2);
* `logShellPaperBExponent` (`floor(log(p e/(p-1))/log p) - 1/e`);
* `padicValNat_sub_div_le_logShellPaperBExponent`;
* `logShellPaperExponent_sum_mul_log_le_three_add_log`;
* `LocalDifferentUpperBound.localDifferentPaperOrder_le_degree_padicVal` (an UPPER bound).

Fact 3 is proved.  Facts 1 and 2 need NEW analytic lemmas: the repo has no
lower bound `d_w >= 1 - 1/e` for the paper different order, and no formal link
`rho_w <= b_w + 1 + [p=2]` from `logShellRadius = sSup(-ordp '' logShell)` to
`logShellPaperBExponent` (the log-shell normalization `(2p)^-1` is not yet
linked to the paper B exponent).  They are recorded as explicit interfaces. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1RhoBoundActual

/-- Fact 3: `-x <= -floor(x)`. -/
theorem neg_le_neg_floor (x : ℝ) : -x ≤ -((⌊x⌋ : ℤ) : ℝ) := by
  have h : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  linarith

/-- Fact 1 interface: `rho <= b + 1 + [p=2]`. -/
def RhoBound (rho b : ℝ) (pIsTwo : Bool) : Prop :=
  rho ≤ b + 1 + (if pIsTwo then 1 else 0 : ℝ)

/-- Fact 2 interface: `1 + [p=2] <= d + a`. -/
def DifferentABound (d a : ℝ) (pIsTwo : Bool) : Prop :=
  1 + (if pIsTwo then 1 else 0 : ℝ) ≤ d + a

/-- Assembly from the two interfaces: `Σrho <= dI+aI+bI` (via sum of fact 1
and fact 2) gives the Step-V inequality. -/
theorem volume_upper_le_of_perPlace
    (rho d a b : ℝ) (pIsTwo : Bool)
    (hrho : RhoBound rho b pIsTwo)
    (hda : DifferentABound d a pIsTwo) :
    rho ≤ d + a + b := by
  unfold RhoBound at hrho
  unfold DifferentABound at hda
  split at hrho <;> split at hda <;> linarith

/-- The floor assembly from A825, restated for completeness. -/
theorem volume_upper_le_floor (lambda dI aI bI sumRho : ℝ)
    (hrho : sumRho ≤ dI + aI + bI) :
    -lambda + sumRho ≤ -((⌊lambda - dI - aI⌋ : ℤ) : ℝ) + bI := by
  have hfloor : ((⌊lambda - dI - aI⌋ : ℤ) : ℝ) ≤ lambda - dI - aI :=
    Int.floor_le (lambda - dI - aI)
  linarith

def rhoRows : List (String × String × String) :=
  [ ("fact 3 floor", "-x <= -floor(x)", "PROVED (neg_le_neg_floor)"),
    ("fact 1 rho", "rho <= b + 1 + [p=2]", "INTERFACE (RhoBound); GAP: link logShellRadius to logShellPaperBExponent"),
    ("fact 2 d+a", "1 + [p=2] <= d + a", "INTERFACE (DifferentABound); GAP: no green lower bound d >= 1-1/e"),
    ("per-place assembly", "rho <= d+a+b from the two interfaces", "PROVED (volume_upper_le_of_perPlace)"),
    ("global assembly", "-lambda+sumrho <= -floor(lambda-dI-aI)+bI", "PROVED (volume_upper_le_floor)"),
    ("green B asset", "logShellPaperBExponent + padicValNat_sub_div_le_logShellPaperBExponent", "GREEN (cited; normalization link missing)"),
    ("green A asset", "logShellPaperAExponent definition/upper bounds", "GREEN (cited; lower d missing)"),
    ("normalization", "log-shell (2p)^-1 log(O^x) vs paper B exponent p: link is the missing analytic lemma", "GAP") ]

theorem rhoRows_length : rhoRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1RhoBoundActual.neg_le_neg_floor
#print axioms LeanFormal.IUT.XiFPaper.Mzk1RhoBoundActual.volume_upper_le_of_perPlace
#print axioms LeanFormal.IUT.XiFPaper.Mzk1RhoBoundActual.volume_upper_le_floor

end LeanFormal.IUT.XiFPaper.Mzk1RhoBoundActual

end