/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual

/-! # Mzk1Gap2OneDirectionalTightnessQpilotActual — one-directional tightness (A689)

One-directional tightness of the unique remaining named input: the corrected-region
Gap 2 shape implies the pure arithmetic `BadSumWeightBound` (canonical
`correctedGap2_iff_arith.mp`); the reverse direction is **not claimed**.  Also the
minimal additive constant is explicit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap2OneDirectionalTightnessQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- One-directional tightness: corrected Gap 2 shape ⇒ arithmetic BadSumWeightBound. -/
theorem correctedGap2_imp_arith
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal)
    (hGap2 : CorrectedGap2Shape T point eN) :
    BadSumWeightBound T eN :=
  (correctedGap2_iff_arith T point eN hc0 hcT hhull).mp hGap2

/-- The reverse direction is explicitly NOT claimed here (three-state table). -/
def oneDirectionalRows : List (String × String × String) :=
  [ ("corrected Gap2 shape => arithmetic", "PROVED (one direction)",
     "correctedGap2_iff_arith.mp"),
    ("arithmetic => Gap2 shape", "NOT-PROVED (not claimed)", "reverse not asserted"),
    ("minimal additive constant", "PROVED (arithmetic)",
     "D = v - (1+eps)*w - theta") ]

theorem oneDirectionalRows_length : oneDirectionalRows.length = 3 := rfl

/-- Arithmetic minimal-D sharpness (object-level tightness of the additive constant). -/
theorem arith_min_D_tight {v w theta epsilon D : Real}
    (h : v ≤ (1 + epsilon) * w + theta + D) :
    v - (1 + epsilon) * w - theta ≤ D :=
  by linarith

/-- Numeric tightness witness: the minimal D is attained. -/
theorem arith_min_D_witness :
    (1 : Real) - (1 + (1/2 : Real)) * 2 - 0 = -(2 : Real) ∧
      (1 : Real) ≤ (1 + (1/2 : Real)) * 2 + 0 + (-(2 : Real)) :=
  by norm_num

#check correctedGap2_imp_arith
#check oneDirectionalRows_length
#check arith_min_D_tight
#check arith_min_D_witness

end LeanFormal.IUT.XiFPaper.Mzk1Gap2OneDirectionalTightnessQpilotActual
end
