/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1IdealMapCompletionIdealActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.external.ported.flt.FLT.DedekindDomain.AdicValuation
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.Tactic

/-! # P1: bridge 2 - localizedLine = span of the ideal-map image; max-ideal span -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedLineIdealMapActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedFractionalIdealActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapCompletionIdealActual
open Multiplicative WithZero

variable {k : Type} [Field k] [NumberField k]

/-- Bridge 2: the localization of an integral ideal is the O_v-span of the image of its
ideal extension. -/
theorem localizedLine_eq_span_idealMap (J : Ideal (NumberField.RingOfIntegers k))
    (v : NumberField.FinitePlace k) :
    localizedLine (k := k) (J : LineBundle (k := k)) v =
      Submodule.span (LocalRing (k := k) v)
        ((fun x : LocalRing (k := k) v => (x : LocalField (k := k) v)) ''
          ((Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v)) J :
            Ideal (LocalRing (k := k) v)) : Set (LocalRing (k := k) v))) := by
  rw [← localizedFractionalIdeal_coe_eq (k := k) (J : LineBundle (k := k)) v]
  have h := FractionalIdeal.extended_coeIdeal_eq_map
    (A := NumberField.RingOfIntegers k) (K := k) (B := LocalRing (k := k) v)
    (M := nonZeroDivisors (NumberField.RingOfIntegers k))
    (N := nonZeroDivisors (LocalRing (k := k) v))
    (L := LocalField (k := k) v)
    (f := algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
    (hf := sourceNZLeComap v) (I₀ := J)
  rw [localizedFractionalIdeal, h]
  rw [FractionalIdeal.coe_coeIdeal, IsLocalization.coeSubmodule]
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  · rw [Submodule.span_le]
    rintro x ⟨y, hy, rfl⟩
    have hfun : ((fun x : LocalRing (k := k) v => (x : LocalField (k := k) v)) =
        ⇑(Algebra.linearMap (LocalRing (k := k) v) (LocalField (k := k) v))) := by
      funext z
      rfl
    rw [hfun]
    change (Algebra.linearMap (LocalRing (k := k) v) (LocalField (k := k) v)) y ∈
      Submodule.map (Algebra.linearMap (LocalRing (k := k) v) (LocalField (k := k) v))
        (Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v)) J)
    rw [Submodule.mem_map]
    exact ⟨y, hy, rfl⟩

/-- Max-ideal span: from bridge 1 + bridge 2 + FLT uniformizer. -/
theorem localizedLine_maxIdeal_eq_span_uniformizer (v : NumberField.FinitePlace k) :
    exists pi : LocalRing (k := k) v,
      Valued.v (pi : LocalField (k := k) v) = ofAdd (-1 : Int) ∧
        localizedLine (k := k)
          (((underlyingPrime v).asIdeal : Ideal (NumberField.RingOfIntegers k)) :
            LineBundle (k := k)) v =
        Submodule.span (LocalRing (k := k) v) {(pi : LocalField (k := k) v)} := by
  obtain ⟨pi, hpi⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer
    (K := k) (v := underlyingPrime v)
  refine ⟨pi, hpi, ?_⟩
  rw [localizedLine_eq_span_idealMap]
  rw [idealMapMaximalBridge_proved (k := k) v]
  have hmax :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
      (K := k) (v := underlyingPrime v) hpi
  have hci : (completionIdealOf (k := k) v : Set (LocalRing (k := k) v)) =
      ((IsLocalRing.maximalIdeal (LocalRing (k := k) v)) : Set (LocalRing (k := k) v)) := rfl
  rw [hci, hmax]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨z, hz, rfl⟩
    have hz' : z ∈ Submodule.span (LocalRing (k := k) v) {(pi : LocalRing (k := k) v)} := hz
    rw [Submodule.mem_span_singleton] at hz'
    obtain ⟨c, hc⟩ := hz'
    rw [← hc]
    change (algebraMap (LocalRing (k := k) v) (LocalField (k := k) v) c) *
        (pi : LocalField (k := k) v) ∈
      Submodule.span (LocalRing (k := k) v) {(pi : LocalField (k := k) v)}
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  · rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Submodule.subset_span ⟨(pi : LocalRing (k := k) v),
      Ideal.subset_span (Set.mem_singleton _), rfl⟩

def localizedLineIdealMapRows : List (String × String × String) :=
  [ ("localizedLine_eq_span_idealMap", "bridge 2: localizedLine = span of ideal-map image", "PROVED (attempt)"),
    ("localizedLine_maxIdeal_eq_span_uniformizer", "max-ideal span{pi} from bridge 1+2+FLT", "PROVED (attempt)") ]

theorem localizedLineIdealMapRows_length : localizedLineIdealMapRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedLineIdealMapActual

end