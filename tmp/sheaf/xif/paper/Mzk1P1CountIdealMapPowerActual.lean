/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealMapPowerGeneralActual
import tmp.sheaf.xif.paper.Mzk1P1IdealMapCompletionIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PrincipalValuationProofActual
import Mathlib.Tactic

/-! # P1: ideal-map power from the maximal bridge (prime powers) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1CountIdealMapPowerActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapCompletionIdealActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable {k : Type} [Field k] [NumberField k]

theorem ideal_map_pow_of_maximalBridge (v : NumberField.FinitePlace k)
    (hbridge : IdealMapMaximalBridge (k := k) v) (n : Nat) :
    Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
      ((underlyingPrime v).asIdeal ^ n) =
      (completionIdealOf (k := k) v) ^ n := by
  rw [ideal_map_pow_general]
  unfold IdealMapMaximalBridge at hbridge
  rw [hbridge]

theorem idealMapPowerStatement_prime_pow (v : NumberField.FinitePlace k)
    (hbridge : IdealMapMaximalBridge (k := k) v) (n : Nat)
    (hn : ((underlyingPrime v).asIdeal ^ n) ≠ 0)
    (hcount : (Associates.mk (underlyingPrime v).asIdeal).count
        (Associates.mk ((underlyingPrime v).asIdeal ^ n)).factors = n) :
    IdealMapPowerStatement (k := k) ((underlyingPrime v).asIdeal ^ n) hn v := by
  apply idealMapPowerStatement_of_count_map
  · exact hcount
  · exact ideal_map_pow_of_maximalBridge (k := k) v hbridge n

def countIdealMapRows : List (String × String × String) :=
  [ ("ideal_map_pow_of_maximalBridge", "map(p^n) = completionIdeal^n from maximal bridge", "PROVED"),
    ("idealMapPowerStatement_prime_pow", "prime power instance of IdealMapPowerStatement", "PROVED (conditional on count fact)") ]

theorem countIdealMapRows_length : countIdealMapRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1CountIdealMapPowerActual

end