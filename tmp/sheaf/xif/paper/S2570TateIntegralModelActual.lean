import tmp.sheaf.xif.paper.S2569TateA6UnconditionalActual
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Valued.NormedValued

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2568TateCoefficientNormActual
open LeanFormal.IUT.XiFPaper.S2569TateA6UnconditionalActual

namespace LeanFormal.IUT.XiFPaper.S2570TateIntegralModelActual

variable {K : Type*} [Field K] [NumberField K]
variable (p : NumberField.FinitePlace K)

noncomputable instance S2570CompletionCompleteSpace : CompleteSpace (Completion p) := by infer_instance

noncomputable instance S2570CompletionNontriviallyNormedField :
    NontriviallyNormedField (Completion p) :=
  Valued.toNontriviallyNormedField (Completion p) (WithZero (Multiplicative Int))

noncomputable def S2570TateIntegralModel (q : Completion p) (hq : ‖q‖ < 1) :
    WeierstrassCurve (CompletionIntegers p) where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := ⟨TateCurve.a4 (Completion p) q, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (Valued.toNormedField.norm_le_one_iff).mp
      (le_of_lt (lt_of_le_of_lt (S2568_norm_a4_le (K := Completion p) hq) hq))⟩
  a₆ := ⟨TateCurve.a6 (Completion p) q, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (Valued.toNormedField.norm_le_one_iff).mp
      (le_of_lt (lt_of_le_of_lt (S2569_norm_a6_le_unconditional (K := Completion p) q hq) hq))⟩

theorem S2570TateIntegralModel_map (q : Completion p) (hq : ‖q‖ < 1) :
    (S2570TateIntegralModel p q hq).map (CompletionIntegers p).subtype =
      TateCurve.weierstrassCurve (Completion p) q := by
  ext <;> simp [S2570TateIntegralModel, TateCurve.weierstrassCurve]

def S2570NodalCubic (R : Type*) [CommRing R] : WeierstrassCurve R := ⟨1, 0, 0, 0, 0⟩

theorem S2570_a4_mem_maximalIdeal (q : Completion p) (hq : ‖q‖ < 1) :
    (⟨TateCurve.a4 (Completion p) q, by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      exact (Valued.toNormedField.norm_le_one_iff).mp
        (le_of_lt (lt_of_le_of_lt (S2568_norm_a4_le (K := Completion p) hq) hq))⟩ :
      CompletionIntegers p) ∈ IsLocalRing.maximalIdeal (CompletionIntegers p) := by
  let y : (Valued.v : Valuation (Completion p) (WithZero (Multiplicative Int))).valuationSubring :=
    ⟨TateCurve.a4 (Completion p) q, by
      rw [Valuation.mem_valuationSubring_iff]
      exact (Valued.toNormedField.norm_le_one_iff).mp
        (le_of_lt (lt_of_le_of_lt (S2568_norm_a4_le (K := Completion p) hq) hq))⟩
  change y ∈ IsLocalRing.maximalIdeal
    ((Valued.v : Valuation (Completion p) (WithZero (Multiplicative Int))).valuationSubring)
  rw [Valuation.mem_maximalIdeal_iff]
  exact (Valued.toNormedField.norm_lt_one_iff).mp
    (lt_of_le_of_lt (S2568_norm_a4_le (K := Completion p) hq) hq)

theorem S2570_a6_mem_maximalIdeal (q : Completion p) (hq : ‖q‖ < 1) :
    (⟨TateCurve.a6 (Completion p) q, by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      exact (Valued.toNormedField.norm_le_one_iff).mp
        (le_of_lt (lt_of_le_of_lt (S2569_norm_a6_le_unconditional (K := Completion p) q hq) hq))⟩ :
      CompletionIntegers p) ∈ IsLocalRing.maximalIdeal (CompletionIntegers p) := by
  let y : (Valued.v : Valuation (Completion p) (WithZero (Multiplicative Int))).valuationSubring :=
    ⟨TateCurve.a6 (Completion p) q, by
      rw [Valuation.mem_valuationSubring_iff]
      exact (Valued.toNormedField.norm_le_one_iff).mp
        (le_of_lt (lt_of_le_of_lt (S2569_norm_a6_le_unconditional (K := Completion p) q hq) hq))⟩
  change y ∈ IsLocalRing.maximalIdeal
    ((Valued.v : Valuation (Completion p) (WithZero (Multiplicative Int))).valuationSubring)
  rw [Valuation.mem_maximalIdeal_iff]
  exact (Valued.toNormedField.norm_lt_one_iff).mp
    (lt_of_le_of_lt (S2569_norm_a6_le_unconditional (K := Completion p) q hq) hq)

theorem S2570TateIntegralModel_reduction (q : Completion p) (hq : ‖q‖ < 1) :
    (S2570TateIntegralModel p q hq).map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (CompletionIntegers p))) =
      S2570NodalCubic (CompletionIntegers p ⧸ IsLocalRing.maximalIdeal (CompletionIntegers p)) := by
  ext <;> simp [S2570TateIntegralModel, S2570NodalCubic, WeierstrassCurve.map,
    Ideal.Quotient.eq_zero_iff_mem, S2570_a4_mem_maximalIdeal p q hq,
    S2570_a6_mem_maximalIdeal p q hq]

#check S2570TateIntegralModel_reduction
#print axioms S2570TateIntegralModel_reduction
#check S2570TateIntegralModel
#check S2570TateIntegralModel_map
#print axioms S2570TateIntegralModel_map
end LeanFormal.IUT.XiFPaper.S2570TateIntegralModelActual
end