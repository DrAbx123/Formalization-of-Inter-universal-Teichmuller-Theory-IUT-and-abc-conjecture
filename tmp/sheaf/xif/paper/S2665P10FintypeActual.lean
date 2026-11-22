import tmp.sheaf.xif.paper.S2663P10PrimeActual
import tmp.sheaf.xif.paper.S2592GenericLocalizedResidueIsoActual
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2665P10FintypeActual
open LeanFormal.IUT.XiFPaper.S2663P10PrimeActual
open LeanFormal.IUT.XiFPaper.S2661P10Actual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2592GenericLocalizedResidueIsoActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
lemma P0_ne_bot (W : S2584PrimeDegreeOneWitness) : P0 W ≠ ⊥ := by
  intro h
  have hunder : (P0 W).under O = q W := (P0_lies W).over.symm
  rw [h, Ideal.under_bot] at hunder
  have hq : q W = W.p := q_eq W
  rw [hq] at hunder
  have hpne : W.p ≠ ⊥ := by
    intro hpbot
    have hspan : W.p.under ℤ = ⊥ := by rw [hpbot, Ideal.under_bot]
    rw [W.p_liesOver.over.symm] at hspan
    have : (Ideal.span ({(613 : ℤ)} : Set ℤ)) ≠ ⊥ := by
      intro hbot
      have : (613 : ℤ) ∈ (⊥ : Ideal ℤ) := by
        rw [← hbot]
        exact Ideal.mem_span_singleton_self 613
      exact (by norm_num : (613 : ℤ) ≠ 0) (by simpa using this)
    exact this hspan
  exact hpne hunder.symm
noncomputable def localizedResidueEquivP10 (W : S2584PrimeDegreeOneWitness) :
    (OL ⧸ P0 W) ≃+* (T10 ⧸ P10 W) := by
  haveI : (P0 W).IsMaximal := S2595LResidueEquivActual.S2595P0_max (D W) (h613 W)
  haveI : (P10 W).IsPrime := P10_prime W
  have hunder : (P10 W).comap (algebraMap OL T10) = P0 W := by
    have hdisj := S2663P10PrimeActual.hdisj W
    have h := IsLocalization.under_map_of_isPrime_disjoint
      (M := Algebra.algebraMapSubmonoid OL (Submonoid.powers (10 : O)))
      (S := T10) (P0_prime W) hdisj
    exact h
  exact localizedResidueEquiv
    (M := Algebra.algebraMapSubmonoid OL (Submonoid.powers (10 : O)))
    (I := P0 W) (P := P10 W) hunder
noncomputable instance P10_fintype (W : S2584PrimeDegreeOneWitness) :
    Fintype (T10 ⧸ P10 W) := by
  haveI : Ring.HasFiniteQuotients OL :=
    Ring.HasFiniteQuotients.of_module_finite (R := ℤ) OL
  haveI : Finite (OL ⧸ P0 W) :=
    Ring.HasFiniteQuotients.finiteQuotient (P0_ne_bot W)
  haveI : Fintype (OL ⧸ P0 W) := Fintype.ofFinite _
  exact Fintype.ofEquiv (OL ⧸ P0 W) (localizedResidueEquivP10 W)
#print axioms P0_ne_bot
#print axioms localizedResidueEquivP10
end LeanFormal.IUT.XiFPaper.S2665P10FintypeActual
end
