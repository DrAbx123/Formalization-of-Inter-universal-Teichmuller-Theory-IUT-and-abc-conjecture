import tmp.sheaf.xif.paper.S2596kCard613Actual
import tmp.sheaf.xif.paper.S2591LocalizedResidueEquivActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596lP0CardActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2596kCard613Actual
open LeanFormal.IUT.XiFPaper.S2591LocalizedResidueEquivActual
lemma h613_of_witness (W : S2584PrimeDegreeOneWitness) :
    (algebraMap ℤ S2565ConcreteIntegralClosureCActual.S) (613 : ℤ) ∈ W.P := by
  rw [← Ideal.mem_comap]
  change (613 : ℤ) ∈ W.P.under ℤ
  rw [← W.P_liesOver.over]
  exact Ideal.mem_span_singleton_self (613 : ℤ)
lemma card_C_quot_p0 (W : S2584PrimeDegreeOneWitness)
    (hirr : S2587FbarIrreducibleRequired W) :
    Nat.card (S2565ConcreteIntegralClosureCActual.C ⧸
      (S2587ResidueDataOfWitness W hirr).p.comap
        (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S)) = 613 := by
  let D := S2587ResidueDataOfWitness W hirr
  have h613 : (algebraMap ℤ S2565ConcreteIntegralClosureCActual.S) (613 : ℤ) ∈ D.p := h613_of_witness W
  have h := Nat.card_congr (S2591_localized_residue_equiv D h613).symm.toEquiv
  rw [show Nat.card (S2565ConcreteIntegralClosureCActual.S ⧸ D.p) = 613 from card_S_quot_D W hirr] at h
  exact h.symm
#print axioms h613_of_witness
#print axioms card_C_quot_p0
end LeanFormal.IUT.XiFPaper.S2596lP0CardActual
end
