/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountActual
import tmp.external.ported.flt.FLT.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic

/-! # P1: Ideal.map of the maximal ideal = completionIdeal (bridge, with proof) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapCompletionIdealActual

open IsDedekindDomain
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open Multiplicative WithZero

variable {k : Type} [Field k] [NumberField k]

def completionIdealOf (v : NumberField.FinitePlace k) :
    Ideal (LocalRing (k := k) v) :=
  IsDedekindDomain.HeightOneSpectrum.completionIdeal k (underlyingPrime v)

def IdealMapMaximalBridge (v : NumberField.FinitePlace k) : Prop :=
  Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
    (underlyingPrime v).asIdeal = completionIdealOf (k := k) v

theorem idealMapMaximalBridge_proved (v : NumberField.FinitePlace k) :
    IdealMapMaximalBridge (k := k) v := by
  let w := underlyingPrime v
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer (v := w)
  have hlt : w.intValuation a < 1 := by
    rw [ha]
    decide
  have hamem : a ∈ w.asIdeal := (w.intValuation_lt_one_iff_mem a).mp hlt
  have hval : Valued.v (((algebraMap (NumberField.RingOfIntegers k)
      (LeanFormal.IUT.NumberFieldFinitePlace.CompletionIntegers v) a :
      LeanFormal.IUT.NumberFieldFinitePlace.CompletionIntegers v)) :
      LeanFormal.IUT.NumberFieldFinitePlace.Completion v) = ofAdd (-1 : Int) := by
    have h1 : Valued.v (((algebraMap (NumberField.RingOfIntegers k)
        (LeanFormal.IUT.NumberFieldFinitePlace.CompletionIntegers v) a :
        LeanFormal.IUT.NumberFieldFinitePlace.CompletionIntegers v)) :
        LeanFormal.IUT.NumberFieldFinitePlace.Completion v) =
        (underlyingPrime v).valuation k (algebraMap (NumberField.RingOfIntegers k) k a) :=
      LeanFormal.IUT.NumberFieldFinitePlace.valued_algebraMap_completionIntegers (place := v) (r := a)
    have h2 : (underlyingPrime v).valuation k
        (algebraMap (NumberField.RingOfIntegers k) k a) = ofAdd (-1 : Int) := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := k) (v := underlyingPrime v)]
      exact ha
    exact h1.trans h2
  have hmax : IsLocalRing.maximalIdeal (LocalRing (k := k) v) =
      Ideal.span {algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v) a} :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
      (K := k) (v := w) hval
  unfold IdealMapMaximalBridge completionIdealOf
  change Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
      (underlyingPrime v).asIdeal = IsLocalRing.maximalIdeal (LocalRing (k := k) v)
  rw [hmax]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    rw [← hmax]
    change (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v) x) ∈
      IsDedekindDomain.HeightOneSpectrum.completionIdeal k w
    rw [IsDedekindDomain.HeightOneSpectrum.mem_completionIdeal_iff (K := k) (v := w)]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_completionIntegers]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := k) (v := w)]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := k) (v := w)]
    exact (w.intValuation_lt_one_iff_mem x).mpr hx
  · rw [Ideal.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Ideal.mem_map_of_mem _ hamem

def idealMapCompletionRows : List (String × String × String) :=
  [ ("IdealMapMaximalBridge", "Ideal.map O_K->O_v p = completionIdeal", "PROVED (attempt)") ]

theorem idealMapCompletionRows_length : idealMapCompletionRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapCompletionIdealActual

end
