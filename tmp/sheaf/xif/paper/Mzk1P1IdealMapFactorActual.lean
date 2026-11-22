/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealMapCompletionIdealActual
import tmp.sheaf.xif.paper.Mzk1P1IdealMapNonVPrimeActual
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic

/-! # P1: per-factor evaluation of the mapped prime-power factorization -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapFactorActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapCompletionIdealActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapNonVPrimeActual
open IsDedekindDomain

variable {k : Type} [Field k] [NumberField k]

/-- The factor at the place `v` maps to the corresponding power of the completion ideal. -/
theorem map_maxPowDividing_self (v : NumberField.FinitePlace k)
    (I : Ideal (NumberField.RingOfIntegers k)) :
    Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
      ((underlyingPrime v).maxPowDividing I) =
    completionIdealOf (k := k) v ^
      (Associates.mk (underlyingPrime v).asIdeal).count (Associates.mk I).factors := by
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, Ideal.map_pow,
    idealMapMaximalBridge_proved (k := k) v]

/-- A factor at another place maps to the unit ideal. -/
theorem map_maxPowDividing_ne_self (v : NumberField.FinitePlace k)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hw : w ≠ underlyingPrime v) (I : Ideal (NumberField.RingOfIntegers k)) :
    Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
      (w.maxPowDividing I) = ⊤ := by
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, Ideal.map_pow,
    ideal_map_nonV_prime_eq_top (k := k) v w hw]
  simp

def factorRows : List (String × String × String) :=
  [ ("map_maxPowDividing_self", "v-factor maps to completionIdeal^count", "PROVED"),
    ("map_maxPowDividing_ne_self", "non-v factor maps to top", "PROVED") ]

theorem factorRows_length : factorRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapFactorActual

end