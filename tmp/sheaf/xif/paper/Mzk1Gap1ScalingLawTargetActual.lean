/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A656 Gap1 SCALING-LAW TARGET on the canonical paper region (mainline)

Goal: reduce Gap 1 to an exact scaling-law hypothesis on the canonical region
`paperComparisonRegion T point a b c`, and prove the arithmetic part so that a
proved scaling law closes Gap 1.

## Honest status of the green scaling laws
* `S2727ScaledRegionVolume_eq_scalingRatio_mul_unit` and
  `S2733ScalingActual.c3LogVolume_smul_norm` are exact scaling laws on the **C3
  log-shell tensor block** carrier `C3LogShellTensorBlock C3`, not on `S1902Carrier T`;
  applying them to our region requires an explicit carrier/region correspondence
  (named hypothesis), which is NOT claimed here.
* On OUR carrier, hull's `Mzk1ScalingDirectionActual` proves the one-dimensional inverse
  prime scaling laws (`prime_inv_smul_measure`, `prime_pow_inv_smul_measure`); the
  product/`badInvScale` form is still being written by hull.

## What is PROVED here
* `gap1_of_scalingLaw_and_arith`: under the exact scaling law of the region and the
  arithmetic inequality, Gap 1 holds (reduction, no gap hidden);
* `gap1_arithmetic_condition_iff`: under the scaling law, Gap 1 is EQUIVALENT to the
  arithmetic inequality `log c <= (1+ε)*(unit + log (ratio a b c) + const)`;
* `gap1_of_fullRatio`: if the scaling law holds with `ratio = a+b+c+1` (FULL N, e.g.
  when all primes of N are at bad places), then Gap 1 holds whenever the unit region
  volume and const are nonnegative.

**This does not prove Gap 1 for the paper region**: the scaling law (and the full-ratio
property) remain named inputs.  ABC gate NOT passed; no canonical object changed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **Exact scaling law of the canonical paper region** (named hypothesis): the region's
  real log-volume equals the unit region's plus `log (ratio a b c)` plus `const`.
  (`ratio` is expected to be the bad-support part, or full `N = a+b+c+1` in the
  favourable case.) -/
def PaperRegionScalingLaw (point : Nat → Nat → Nat → S1902Carrier T)
    (ratio : Nat → Nat → Nat → ℝ) (const : ℝ) : Prop :=
  ∀ a b c : Nat,
    (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal =
      (s1902LogVolume T (s1902UnitRegion T)).toReal + Real.log (ratio a b c) + const

/-- **Reduction**: exact scaling law + arithmetic inequality ⇒ Gap 1 pointwise. -/
theorem gap1_of_scalingLaw_and_arith
    (point : Nat → Nat → Nat → S1902Carrier T)
    (ratio : Nat → Nat → Nat → ℝ) (const ε : ℝ) (hε : 0 < ε)
    (hvol : PaperRegionScalingLaw T point ratio const)
    (harith : ∀ a b c : Nat, IsABCTriple a b c →
      Real.log (c : ℝ) ≤
        (1 + ε) * ((s1902LogVolume T (s1902UnitRegion T)).toReal +
          Real.log (ratio a b c) + const)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) *
          (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal := by
  intro a b c habc
  rw [hvol a b c]
  rw [show Height.logHeight₁ (abcRationalPoint a c) = Real.log (c : ℝ) from
    abcRationalPoint_logHeight₁ habc]
  exact harith a b c habc

/-- **Equivalence**: under the scaling law, Gap 1 is exactly the arithmetic inequality
  (no gap hidden). -/
theorem gap1_arithmetic_condition_iff
    (point : Nat → Nat → Nat → S1902Carrier T)
    (ratio : Nat → Nat → Nat → ℝ) (const ε : ℝ) (hε : 0 < ε)
    (hvol : PaperRegionScalingLaw T point ratio const) :
    (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + ε) *
            (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal) ↔
      (∀ a b c : Nat, IsABCTriple a b c →
        Real.log (c : ℝ) ≤
          (1 + ε) * ((s1902LogVolume T (s1902UnitRegion T)).toReal +
            Real.log (ratio a b c) + const)) := by
  constructor
  · intro h a b c habc
    have h1 := h a b c habc
    rw [show Height.logHeight₁ (abcRationalPoint a c) = Real.log (c : ℝ) from
      abcRationalPoint_logHeight₁ habc] at h1
    rwa [hvol a b c] at h1
  · intro h
    exact gap1_of_scalingLaw_and_arith T point ratio const ε hε hvol h

/-- The full-ratio candidate: `ratio = a + b + c + 1` (all primes of `N` at bad places). -/
def FullRatio : Nat → Nat → Nat → ℝ :=
  fun a b c => (((a + b + c + 1 : ℕ)) : ℝ)

/-- Arithmetic core: `log c <= log (a+b+c+1)` on ABC triples. -/
theorem log_abc_c_le_log_N {a b c : Nat} (habc : IsABCTriple a b c) :
    Real.log (c : ℝ) ≤ Real.log (((a + b + c + 1 : ℕ)) : ℝ) :=
  Real.log_le_log (by exact_mod_cast habc.c_pos)
    (by
      have hnat : c ≤ a + b + c + 1 := by omega
      exact_mod_cast hnat)

/-- **Gap 1 from a FULL-ratio scaling law**: if the region's scaling law uses the full
  `a+b+c+1`, and unit region volume / const are nonnegative, then Gap 1 holds. -/
theorem gap1_of_fullRatio
    (point : Nat → Nat → Nat → S1902Carrier T) (const ε : ℝ) (hε : 0 < ε)
    (hvol : PaperRegionScalingLaw T point FullRatio const)
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hconst : 0 ≤ const) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) *
          (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal := by
  refine gap1_of_scalingLaw_and_arith T point FullRatio const ε hε hvol ?_
  intro a b c habc
  rw [show FullRatio a b c = (((a + b + c + 1 : ℕ)) : ℝ) from rfl]
  have hlogc := log_abc_c_le_log_N habc
  have hNpos : (0 : ℝ) < (((a + b + c + 1 : ℕ)) : ℝ) := by
    have : 0 < a + b + c + 1 := Nat.succ_pos _
    exact_mod_cast this
  have hlogN : 0 ≤ Real.log (((a + b + c + 1 : ℕ)) : ℝ) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ (((a + b + c + 1 : ℕ)) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    simpa using this)
  have hX : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal +
      Real.log ((((a + b + c + 1 : ℕ)) : ℝ)) + const := by linarith
  have hle1 : (1 : ℝ) ≤ 1 + ε := by linarith
  have hcoef : Real.log ((((a + b + c + 1 : ℕ)) : ℝ)) ≤
      (1 + ε) * ((s1902LogVolume T (s1902UnitRegion T)).toReal +
        Real.log ((((a + b + c + 1 : ℕ)) : ℝ)) + const) := by
    have h1 : (1 : ℝ) * Real.log ((((a + b + c + 1 : ℕ)) : ℝ)) ≤
        (1 + ε) * ((s1902LogVolume T (s1902UnitRegion T)).toReal +
          Real.log ((((a + b + c + 1 : ℕ)) : ℝ)) + const) :=
      mul_le_mul hle1 (by linarith) hlogN (by linarith)
    simpa using h1
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual.gap1_of_scalingLaw_and_arith
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual.gap1_arithmetic_condition_iff
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual.gap1_of_fullRatio