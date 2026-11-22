/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import tmp.sheaf.xif.paper.Mzk1SelfContainedGap1QpilotActual
import tmp.sheaf.xif.paper.Mzk1Gap2ShapeABCStrengthQpilotActual
import tmp.sheaf.xif.paper.Mzk1CorrectedGap2ABCQpilotActual
import tmp.sheaf.xif.paper.Mzk1A703CorrectionQpilotActual
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import Mathlib.Tactic

/-! # Mzk1FinalBoundaryV2QpilotActual — FinalBoundary V2 (A688 + A703 retraction)

Version-2 final boundary table.  A703 (user review) RETRACTS the hfull-based
`final_conditional_ABC` / `natRadicalWeightBound_iff_ABC` as vacuous (hfull is
unsatisfiable for fixed T), declares the N = a+b+c+1 scaling NOT the paper
structure, and re-specifies the named input via triple-dependent Θ-data
(N1: `q = (abc)^2`, bad primes = primes(abc), normalized weights).  Historical rows
are retained and annotated RETRACTED; new N1 rows are added. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryV2QpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1SelfContainedGap1QpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ShapeABCStrengthQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ABCQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1A703CorrectionQpilotActual
open scoped ENNReal BigOperators

universe u

/-- V2 final boundary table with A703 RETRACTED annotations and N1 rows. -/
def finalBoundaryV2Rows : List (String × String × String) :=
  [ ("Cor 3.12 requirement chain", "PROVED-CHAIN (not load-bearing, A703)",
     "A703: 3.12 chain has no thetaReading upper bound"),
    ("corrected-region Gap 1", "PROVED (theorem, still valid)",
     "corrected_gap1_unconditional (Mathlib-only, no hfull)"),
    ("corrected Gap 2 shape => ABC (hfull route)", "RETRACTED (A703)",
     "hfull unsatisfiable for fixed T => vacuous"),
    ("corrected-region Gap 2 shape", "NAMED (re-specified via N1)",
     "triple-dependent Theta-data, no N-scaling"),
    ("reverse: ABC => Gap 2", "NOT-PROVED (not claimed)", "no reverse implication"),
    ("ABC gate", "NOT-PASSED", "conditional closure only"),
    ("BadSumWeightBound natRadical explicitization",
     "IDENTITY STILL VALID; N-scaling usage RETRACTED",
     "dictionary identity separate from retracted route"),
    ("N1: q = (abc)^2 and q_log = 2 log(abc)", "CORRECTED SPEC (A703)",
     "CorrectedTripleThetaData.q_def / qLog_eq"),
    ("N1: (1/6) log q = (1/3) log(abc)", "PROVED (A703, Mathlib-only)",
     "sixth_qLog_eq_third_log_abc"),
    ("N1: bad primes = primes(abc)", "CORRECTED SPEC (A703)",
     "badSupport_eq (no hfull)"),
    ("N1: normalized weight sum_{p|abc} log p", "CORRECTED SPEC (A703)",
     "normalizedWeight"),
    ("retraction record", "RETRACTED LIST (A703)",
     "a703StatusRows / retractedQpilotFiles") ]

theorem finalBoundaryV2Rows_length : finalBoundaryV2Rows.length = 12 := rfl

/-- V2 final boundary payload: valid Mathlib-only pieces + A703 corrected data. -/
structure FinalBoundaryV2 where
  /-- canonical equivalence: corrected Gap 2 shape ⇔ pure arithmetic BadSumWeightBound. -/
  gap2Arith : ∀ {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [Nonempty (Bad (nativePlaceSelection T))]
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal),
    CorrectedGap2Shape T point eN ↔ BadSumWeightBound T eN
  /-- corrected-region Gap 1 unconditional equivalence (Mathlib-only theorem). -/
  gap1Theorem : ∀ {ι : Type u} [Fintype ι] {h epsilon : Real}
    (f : ι → Real) (e : ι → Nat) (base : Real) (hf : ∀ i, 0 < f i)
    (hb : 0 < base) (hh : 0 < h) (heps : 0 < 1 + epsilon),
    (h ≤ (1 + epsilon) * Mzk1SelfContainedGap1QpilotActual.correctedVol f e base) ↔
      (Real.log h ≤ Real.log (1 + epsilon) +
        (Real.log base - ∑ i, (e i : Real) * Real.log (f i)))
  /-- Gap 2 shape decomposition (base + slack). -/
  gap2Decompose : ∀ {v w theta D epsilon : Real},
    (v ≤ (1 + epsilon) * w + theta + D) ↔ (v ≤ w + (epsilon * w + theta + D))
  /-- Per-ε form does not imply a uniform additive constant. -/
  gap2PerEpsNotUniform :
    ¬ (∃ D : Real, ∀ epsilon : Real, 0 < epsilon →
        1 ≤ (1 + epsilon) * (-1 : Real) + 0 + D)
  /-- A703 corrected arithmetic coherence `(1/6) log q = (1/3) log(abc)`. -/
  sixthLogCoherence : ∀ {a b c : Nat} (D : CorrectedTripleThetaData a b c)
    (habc : 0 < a * b * c), D.qLog / 6 = Real.log (a * b * c) / 3
  rows : finalBoundaryV2Rows.length = 12

/-- The constructed V2 final boundary payload. -/
noncomputable def finalBoundaryV2 : FinalBoundaryV2 where
  gap2Arith := fun {l} T _inst _ne point eN hc0 hcT hhull =>
    correctedGap2_iff_arith T point eN hc0 hcT hhull
  gap1Theorem := fun {ι} _inst {h} {epsilon} f e base hf hb hh heps =>
    corrected_gap1_unconditional f e base hf hb hh heps
  gap2Decompose := fun {v} {w} {theta} {D} {epsilon} => gap2_decompose
  gap2PerEpsNotUniform := gap2_perEpsilon_not_uniform
  sixthLogCoherence := fun {a} {b} {c} D habc => sixth_qLog_eq_third_log_abc D habc
  rows := finalBoundaryV2Rows_length

#check finalBoundaryV2

end LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryV2QpilotActual
end
