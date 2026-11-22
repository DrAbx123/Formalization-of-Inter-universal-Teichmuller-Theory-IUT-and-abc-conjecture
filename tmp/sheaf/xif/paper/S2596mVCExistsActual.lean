import tmp.sheaf.xif.paper.S2596lP0CardActual
import tmp.sheaf.xif.paper.S2590LocalizedPrimeContractionActual
import tmp.sheaf.xif.paper.S2595LResidueEquivActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596mVCExistsActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2590LocalizedPrimeContractionActual
open LeanFormal.IUT.XiFPaper.S2591LocalizedResidueEquivActual
open LeanFormal.IUT.XiFPaper.S2596kCard613Actual
open LeanFormal.IUT.XiFPaper.S2596lP0CardActual
open LeanFormal.IUT.XiFPaper.S2595LResidueEquivActual
lemma exists_vC
    (W : S2584PrimeDegreeOneWitness)
    (hirr : S2587FbarIrreducibleRequired W) :
    ∃ b : S2565ConcreteIntegralClosureCActual.C,
      Ideal.Quotient.mk
          ((S2587ResidueDataOfWitness W hirr).p.comap
            (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S)) b *
        Ideal.Quotient.mk
          ((S2587ResidueDataOfWitness W hirr).p.comap
            (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S))
          (S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C) = 1 := by
  let D := S2587ResidueDataOfWitness W hirr
  let p0 := D.p.comap (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S)
  have h613 : (algebraMap ℤ S2565ConcreteIntegralClosureCActual.S) (613 : ℤ) ∈ D.p :=
    h613_of_witness W
  haveI hmax : p0.IsMaximal := S2590_contraction_maximal D h613
  have hnot : (S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C) ∉ p0 :=
    S2595_Cden_not_mem_q D
  let J : Ideal S2565ConcreteIntegralClosureCActual.C :=
    p0 ⊔ Ideal.span {(S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C)}
  have haJ : (S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C) ∈ J :=
    Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hle : p0 ≤ J := le_sup_left
  have h1 : (1 : S2565ConcreteIntegralClosureCActual.C) ∈ J :=
    (Ideal.isMaximal_iff.mp hmax).2 J
      (S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C) hle hnot haJ
  rw [Submodule.mem_sup] at h1
  obtain ⟨p, hp, z, hz, hpz⟩ := h1
  rw [Ideal.mem_span_singleton] at hz
  obtain ⟨b, hb⟩ := hz
  refine ⟨b, ?_⟩
  have hzq : Ideal.Quotient.mk p0 z = 1 := by
    have h := congrArg (Ideal.Quotient.mk p0) hpz
    rw [map_add, map_one] at h
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hp, zero_add] at h
    exact h
  rw [hb, map_mul] at hzq
  rw [mul_comm]
  exact hzq
lemma vC_pow_613
    (W : S2584PrimeDegreeOneWitness)
    (hirr : S2587FbarIrreducibleRequired W)
    (hnot : (S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C) ∉
      (S2587ResidueDataOfWitness W hirr).p.comap
        (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S)) :
    ∀ b : S2565ConcreteIntegralClosureCActual.C,
      Ideal.Quotient.mk
          ((S2587ResidueDataOfWitness W hirr).p.comap
            (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S)) b *
        Ideal.Quotient.mk
          ((S2587ResidueDataOfWitness W hirr).p.comap
            (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S))
          (S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C) = 1 →
      (Ideal.Quotient.mk
          ((S2587ResidueDataOfWitness W hirr).p.comap
            (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S)) b) ^ 613 =
        Ideal.Quotient.mk
          ((S2587ResidueDataOfWitness W hirr).p.comap
            (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S)) b := by
  let D := S2587ResidueDataOfWitness W hirr
  let p0 := D.p.comap (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S)
  have h613 : (algebraMap ℤ S2565ConcreteIntegralClosureCActual.S) (613 : ℤ) ∈ D.p :=
    h613_of_witness W
  haveI hmax : p0.IsMaximal := S2590_contraction_maximal D h613
  haveI : Field (S2565ConcreteIntegralClosureCActual.C ⧸ p0) :=
    Ideal.Quotient.field p0
  haveI : Fintype (S2565ConcreteIntegralClosureCActual.C ⧸ p0) :=
    Fintype.ofFinite (S2565ConcreteIntegralClosureCActual.C ⧸ p0)
  intro b hb
  have hcard' : Fintype.card (S2565ConcreteIntegralClosureCActual.C ⧸ p0) = 613 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_C_quot_p0 W hirr
  rw [← hcard']
  exact FiniteField.pow_card (K := S2565ConcreteIntegralClosureCActual.C ⧸ p0) (Ideal.Quotient.mk p0 b)
#print axioms exists_vC
#print axioms vC_pow_613
end LeanFormal.IUT.XiFPaper.S2596mVCExistsActual
end
