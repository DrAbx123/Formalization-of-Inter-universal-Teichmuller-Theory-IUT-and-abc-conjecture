/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import LeanFormal.IUT.Foundations.NumberField.SourceQvClosed
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-! # P1: localizedLine as an actual FractionalIdeal over the DVR

Uses `FractionalIdeal.extended` along O_K -> LocalRing to construct the actual
fractional ideal whose coercion is `localizedLine`, then the Mathlib instance
`FractionalIdeal.isPrincipal` over the PID `LocalRing` gives IsPrincipal.
-/

noncomputable section
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedFractionalIdealActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open IsDedekindDomain
open LeanFormal.IUT.NumberFieldFinitePlace
open IsLocalization

variable {k : Type} [Field k] [NumberField k]

/-- Nonzero divisors of O_K map into nonzero divisors of the completed DVR. -/
noncomputable def sourceNZLeComap
    (v : NumberField.FinitePlace k) :
    nonZeroDivisors (NumberField.RingOfIntegers k) ≤
      (nonZeroDivisors (LocalRing (k := k) v)).comap
        (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v)) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (FaithfulSMul.algebraMap_injective _ _)

/-- The localization map from k to LocalField along O_K -> LocalRing. -/
noncomputable def localizedMap (v : NumberField.FinitePlace k) :
    k →+* LocalField (k := k) v :=
  IsLocalization.map (S := k) (LocalField (k := k) v)
    (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
    (sourceNZLeComap v)

/-- The actual fractional ideal over the DVR whose coercion is localizedLine. -/
noncomputable def localizedFractionalIdeal
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) :
    FractionalIdeal (nonZeroDivisors (LocalRing (k := k) v))
      (LocalField (k := k) v) :=
  FractionalIdeal.extended (A := NumberField.RingOfIntegers k)
    (B := LocalRing (k := k) v) (f := algebraMap _ _)
    (K := k) (M := nonZeroDivisors (NumberField.RingOfIntegers k))
    (L := LocalField (k := k) v)
    (N := nonZeroDivisors (LocalRing (k := k) v))
    (sourceNZLeComap v) I

theorem localizedMap_eq_algebraMap (v : NumberField.FinitePlace k) :
    localizedMap (k := k) v = algebraMap k (LocalField (k := k) v) := by
  haveI : IsScalarTower (NumberField.RingOfIntegers k)
      (NumberFieldFinitePlace.CompletionIntegers v)
      (NumberFieldFinitePlace.Completion v) :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsScalarTower'
      (R := NumberField.RingOfIntegers k) (K := k) (v := v.maximalIdeal)
  apply IsLocalization.ringHom_ext
    (M := nonZeroDivisors (NumberField.RingOfIntegers k))
  ext a
  simp only [RingHom.comp_apply, localizedMap, IsLocalization.map_eq]
  have hx : algebraMap k (LocalField (k := k) v)
      ((algebraMap (NumberField.RingOfIntegers k) k) a) =
      ((algebraMap (NumberField.RingOfIntegers k) k a : k) :
        NumberFieldFinitePlace.Completion v) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    rfl
  rw [hx]
  simp [HeightOneSpectrum.algebraMap_adicCompletion]

theorem localizedFractionalIdeal_coe_eq
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) :
    (localizedFractionalIdeal (k := k) I v :
      Submodule (LocalRing (k := k) v) (LocalField (k := k) v)) =
      localizedLine (k := k) I v := by
  rw [localizedFractionalIdeal, FractionalIdeal.coe_extended_eq_span]
  change Submodule.span (LocalRing (k := k) v)
      (localizedMap (k := k) v '' (I : Set k)) =
    Submodule.span (LocalRing (k := k) v)
      ((fun x : k => algebraMap k (LocalField (k := k) v) x) '' (I : Set k))
  rw [localizedMap_eq_algebraMap]

/-- Actual IsPrincipal instance for localizedLine, from the fractional-ideal PID
instance over the completed DVR. -/
theorem localizedLine_isPrincipal_actual
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) :
    (localizedLine (k := k) I v).IsPrincipal := by
  have h : (localizedFractionalIdeal (k := k) I v :
      Submodule (LocalRing (k := k) v) (LocalField (k := k) v)).IsPrincipal :=
    inferInstance
  rwa [localizedFractionalIdeal_coe_eq] at h

def localizedFractionalRows : List (String × String × String) :=
  [ ("localizedMap_eq_algebraMap", "localization map = algebraMap", "PROVED"),
    ("localizedFractionalIdeal_coe_eq", "FractionalIdeal.extended coercion = localizedLine", "PROVED"),
    ("localizedLine_isPrincipal_actual", "actual IsPrincipal for localizedLine", "PROVED (PID instance)") ]

theorem localizedFractionalRows_length : localizedFractionalRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedFractionalIdealActual
