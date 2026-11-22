import tmp.sheaf.xif.paper.S2596mVCExistsActual2
import tmp.sheaf.xif.paper.S2596lP0CardActual
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596nVCPowActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2591LocalizedResidueEquivActual
open LeanFormal.IUT.XiFPaper.S2590LocalizedPrimeContractionActual
open LeanFormal.IUT.XiFPaper.S2596lP0CardActual
lemma vC_pow_613
    (W : S2584PrimeDegreeOneWitness)
    (hirr : S2587FbarIrreducibleRequired W) :
    ∀ b : S2565ConcreteIntegralClosureCActual.C,
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
  intro b
  let e : (S2565ConcreteIntegralClosureCActual.C ⧸ p0) ≃+* ZMod 613 :=
    (S2591_localized_residue_equiv D h613).trans W.residueEquivS
  have hfix : (e (Ideal.Quotient.mk p0 b)) ^ 613 = e (Ideal.Quotient.mk p0 b) := by
    exact FiniteField.pow_card (K := ZMod 613) (e (Ideal.Quotient.mk p0 b))
  apply e.injective
  rw [map_pow, hfix]
#print axioms vC_pow_613
end LeanFormal.IUT.XiFPaper.S2596nVCPowActual
end
