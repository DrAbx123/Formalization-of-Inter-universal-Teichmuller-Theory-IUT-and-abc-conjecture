/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1PrincipalValuationActual
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: principal count <-> local valuation (actual proof, probe-informed) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1PrincipalValuationProofActual

open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1PrincipalValuationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain

variable {k : Type} [Field k] [NumberField k]

theorem principalValuation_proved (a : NumberField.RingOfIntegers k) (ha : a ≠ 0)
    (v : NumberField.FinitePlace k) :
    localValuation (k := k) v
        (algebraMap k (LocalField (k := k) v) a) =
      - (((Associates.mk v.maximalIdeal.asIdeal).count
          (Associates.mk (Ideal.span {a})).factors : Nat) : Int) := by
  haveI : IsScalarTower (NumberField.RingOfIntegers k)
      (NumberFieldFinitePlace.CompletionIntegers v) (NumberFieldFinitePlace.Completion v) :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsScalarTower'
      (R := NumberField.RingOfIntegers k) (K := k) (v := underlyingPrime v)
  unfold localValuation
  have hx : algebraMap k (LocalField (k := k) v) a =
      ((algebraMap (NumberField.RingOfIntegers k) k a : k) :
        NumberFieldFinitePlace.Completion v) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    rfl
  rw [hx]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (K := k) (v := underlyingPrime v)
    (algebraMap (NumberField.RingOfIntegers k) k a)]
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  rw [HeightOneSpectrum.intValuation_if_neg (v := underlyingPrime v) ha]
  rw [WithZero.log_exp]

theorem principalValuationStatement_proved :
    PrincipalValuationStatement (k := k) := by
  intro a ha v
  exact principalValuation_proved a ha v

def principalValuationProofRows : List (String × String × String) :=
  [ ("principalValuation_proved", "localValuation (algebraMap a) = -count_v(span{a})", "PROVED"),
    ("principalValuationStatement_proved", "PrincipalValuationStatement closed", "PROVED") ]

theorem principalValuationProofRows_length : principalValuationProofRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1PrincipalValuationProofActual

end