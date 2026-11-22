import tmp.sheaf.xif.paper.S2596nVCPowActual
import tmp.sheaf.xif.paper.S2596iResidueNatActual
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596oUPowActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2591LocalizedResidueEquivActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2595LResidueEquivActual
open LeanFormal.IUT.XiFPaper.S2590LocalizedPrimeContractionActual
open LeanFormal.IUT.XiFPaper.S2596kCard613Actual
open LeanFormal.IUT.XiFPaper.S2596lP0CardActual
open LeanFormal.IUT.XiFPaper.S2596mVCExistsActual
open LeanFormal.IUT.XiFPaper.S2596nVCPowActual
open LeanFormal.IUT.XiFPaper.S2596iResidueNatActual
open LeanFormal.IUT.XiFPaper.S2596gResidueCompatActual
open LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual
open LeanFormal.IUT.XiFPaper.S2596dHfixActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
lemma u_pow_613
    (W : S2584PrimeDegreeOneWitness)
    (hirr : S2587FbarIrreducibleRequired W) :
    (Ideal.Quotient.mk
        (S2594P (S2595P0 (S2587ResidueDataOfWitness W hirr) (h613_of_witness W)))
        S2596cDenomClearActual.u) ^ 613 =
      Ideal.Quotient.mk
        (S2594P (S2595P0 (S2587ResidueDataOfWitness W hirr) (h613_of_witness W)))
        S2596cDenomClearActual.u := by
  let D := S2587ResidueDataOfWitness W hirr
  let p0 := D.p.comap (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S)
  have h613 : (algebraMap ℤ S2565ConcreteIntegralClosureCActual.S) (613 : ℤ) ∈ D.p :=
    h613_of_witness W
  let P0 := S2595P0 D h613
  let PT := S2594P P0
  have hunder : P0.comap (algebraMap S2565ConcreteIntegralClosureCActual.C S2594LP0PActual.OL) = p0 := by
    simpa [Ideal.under, p0] using (S2595P0_lies D h613).over.symm
  let phi : (S2565ConcreteIntegralClosureCActual.C ⧸ p0) →+* (S2594LP0PActual.OL ⧸ P0) :=
    Ideal.quotientMap P0 (algebraMap S2565ConcreteIntegralClosureCActual.C S2594LP0PActual.OL)
      (le_of_eq hunder.symm)
  obtain ⟨b, hb⟩ := exists_vC W hirr
  have hphi_b : phi (Ideal.Quotient.mk p0 b) =
      Ideal.Quotient.mk P0 (algebraMap S2565ConcreteIntegralClosureCActual.C S2594LP0PActual.OL b) :=
    Ideal.quotientMap_mk
  have hpow : (Ideal.Quotient.mk P0 (algebraMap S2565ConcreteIntegralClosureCActual.C S2594LP0PActual.OL b)) ^ 613 =
      Ideal.Quotient.mk P0 (algebraMap S2565ConcreteIntegralClosureCActual.C S2594LP0PActual.OL b) := by
    have h := congrArg phi (vC_pow_613 W hirr b)
    rw [map_pow, hphi_b] at h
    exact h
  have hv : Ideal.Quotient.mk P0 (algebraMap S2565ConcreteIntegralClosureCActual.C S2594LP0PActual.OL b) *
      Ideal.Quotient.mk P0 S2596cDenomClearActual.aOL = 1 := by
    have h := congrArg phi hb
    rw [map_mul, map_one, hphi_b] at h
    have haC : phi (Ideal.Quotient.mk p0 (S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C)) =
        Ideal.Quotient.mk P0 S2596cDenomClearActual.aOL := by
      rw [Ideal.quotientMap_mk]
    rwa [haC] at h
  have hL := S2595LResidueEquiv_u D h613
    (algebraMap S2565ConcreteIntegralClosureCActual.C S2594LP0PActual.OL b) hv
  have hfin := congrArg (S2595LResidueEquiv D h613) hpow
  rw [map_pow, hL] at hfin
  exact hfin
#print axioms u_pow_613
end LeanFormal.IUT.XiFPaper.S2596oUPowActual
end
