/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealMapCompletionIdealActual
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic

/-! # P1: non-v prime factors map to the unit ideal -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapNonVPrimeActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapCompletionIdealActual
open IsDedekindDomain

variable {k : Type} [Field k] [NumberField k]

/-- For `w ≠ v`, the extension of the prime ideal `w` to the completed DVR is the unit
ideal. -/
theorem ideal_map_nonV_prime_eq_top (v : NumberField.FinitePlace k)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hw : w ≠ underlyingPrime v) :
    Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
      w.asIdeal = ⊤ := by
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : (underlyingPrime v).asIdeal.IsMaximal := (underlyingPrime v).isMaximal
  have hne : w.asIdeal ≠ (underlyingPrime v).asIdeal := by
    intro h
    exact hw (HeightOneSpectrum.ext h)
  have hsup : w.asIdeal ⊔ (underlyingPrime v).asIdeal = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp (Ideal.isCoprime_of_isMaximal hne)
  have hmap := congrArg
    (Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))) hsup
  rw [Ideal.map_top, Ideal.map_sup,
    idealMapMaximalBridge_proved (k := k) v] at hmap
  by_contra hJ
  have hle : Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
      w.asIdeal ≤ IsLocalRing.maximalIdeal (LocalRing (k := k) v) :=
    IsLocalRing.le_maximalIdeal hJ
  have hle2 : Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
      w.asIdeal ⊔ completionIdealOf (k := k) v ≤
      IsLocalRing.maximalIdeal (LocalRing (k := k) v) := by
    refine sup_le hle ?_
    show completionIdealOf (k := k) v ≤ IsLocalRing.maximalIdeal (LocalRing (k := k) v)
    rfl
  rw [hmap] at hle2
  exact (Ideal.IsMaximal.ne_top inferInstance) (top_le_iff.mp hle2)

def nonVPrimeRows : List (String × String × String) :=
  [ ("ideal_map_nonV_prime_eq_top", "map f w.asIdeal = top for w != v", "PROVED") ]

theorem nonVPrimeRows_length : nonVPrimeRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapNonVPrimeActual

end