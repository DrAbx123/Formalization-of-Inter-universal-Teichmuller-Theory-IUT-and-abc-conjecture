/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountProofActual
import tmp.external.ported.flt.FLT.DedekindDomain.AdicValuation
import Mathlib.Tactic

/-! # P1: uniformizer power span (GAP bridge 3) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1UniformizerPowerSpanActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual
open IsDedekindDomain

variable {k : Type} [Field k] [NumberField k]

/-- GAP bridge 3: the span of the `e`-th power of the completion ideal is the span of
the `e`-th power of any uniformizer. -/
theorem uniformizerPowerSpan_proved (v : NumberField.FinitePlace k) :
    UniformizerPowerSpanStatement (k := k) v := by
  intro pi hpi e
  have hmax :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
      (K := k) (v := underlyingPrime v) hpi
  have hpow : completionIdealOf (k := k) v ^ e =
      Ideal.span {((pi : LocalRing (k := k) v) ^ e)} := by
    rw [show completionIdealOf (k := k) v =
      IsLocalRing.maximalIdeal (LocalRing (k := k) v) from rfl, hmax,
      Ideal.span_singleton_pow]
  rw [hpow]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨z, hz, rfl⟩
    have hz' : z ∈ Ideal.span {((pi : LocalRing (k := k) v) ^ e)} := hz
    rw [Ideal.mem_span_singleton] at hz'
    obtain ⟨c, rfl⟩ := hz'
    change (↑((pi : LocalRing (k := k) v) ^ e * c) : LocalField (k := k) v) ∈
      Submodule.span (LocalRing (k := k) v) {((pi : LocalField (k := k) v) ^ e)}
    rw [Subring.coe_mul]
    rw [show (↑((pi : LocalRing (k := k) v) ^ e) : LocalField (k := k) v) =
        (↑(pi : LocalRing (k := k) v) : LocalField (k := k) v) ^ e from by
      simpa using map_pow (algebraMap (LocalRing (k := k) v) (LocalField (k := k) v))
        ((pi : LocalRing (k := k) v)) e]
    rw [mul_comm]
    change (algebraMap (LocalRing (k := k) v) (LocalField (k := k) v) c) *
        ((pi : LocalField (k := k) v) ^ e) ∈
      Submodule.span (LocalRing (k := k) v) {((pi : LocalField (k := k) v) ^ e)}
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  · rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Submodule.subset_span ⟨((pi : LocalRing (k := k) v) ^ e),
      Ideal.subset_span (Set.mem_singleton _), by
        simpa using map_pow (algebraMap (LocalRing (k := k) v) (LocalField (k := k) v))
          ((pi : LocalRing (k := k) v)) e⟩

def powerSpanRows : List (String × String × String) :=
  [ ("uniformizerPowerSpan_proved", "GAP bridge 3: span completionIdeal^e = span pi^e", "PROVED") ]

theorem powerSpanRows_length : powerSpanRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1UniformizerPowerSpanActual

end