import tmp.sheaf.xif.paper.S2596oUPowActual
import tmp.sheaf.xif.paper.S2596fSmulUActual
import tmp.sheaf.xif.paper.S2382ArithFrobDoneActual
import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596pReductionActual
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
open LeanFormal.IUT.XiFPaper.S2596oUPowActual
open LeanFormal.IUT.XiFPaper.S2596iResidueNatActual
open LeanFormal.IUT.XiFPaper.S2596gResidueCompatActual
open LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual
open LeanFormal.IUT.XiFPaper.S2596fSmulUActual
open LeanFormal.IUT.XiFPaper.S2596dHfixActual
open LeanFormal.IUT.XiFPaper.S2596cDenomClearActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
open LeanFormal.IUT.XiFPaper.S2382ArithFrobDoneActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
local instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) S2594LP0PActual.OL :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instMulSemiringActionAlgEquivRingOfIntegers_tmp S1720Field S2057FiveDivisionField
local instance : SMulCommClass Gal(S2057FiveDivisionField/S1720Field)
    (RingOfIntegers S1720Field) S2594LP0PActual.OL :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instSMulCommClassAlgEquivRingOfIntegers_tmp S1720Field S2057FiveDivisionField
theorem localized_reduction_W
    (W : S2584PrimeDegreeOneWitness)
    (hirr : S2587FbarIrreducibleRequired W)
    (sigma : Gal(S2057FiveDivisionField/S1720Field))
    (H : IsArithFrobAt (RingOfIntegers S1720Field) sigma
      (S2595P0 (S2587ResidueDataOfWitness W hirr) (h613_of_witness W)))
    (a : S2594LP0PActual.T) :
    Ideal.Quotient.mk
        (S2594P (S2595P0 (S2587ResidueDataOfWitness W hirr) (h613_of_witness W)))
        (sigmaRingEquiv sigma a) =
      frobBar
        (p := (S2587ResidueDataOfWitness W hirr).p)
        (P := S2594P (S2595P0 (S2587ResidueDataOfWitness W hirr) (h613_of_witness W)))
        (Ideal.Quotient.mk
          (S2594P (S2595P0 (S2587ResidueDataOfWitness W hirr) (h613_of_witness W))) a) := by
  let D := S2587ResidueDataOfWitness W hirr
  let p0 := D.p.comap (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S)
  have h613 : (algebraMap ℤ S2565ConcreteIntegralClosureCActual.S) (613 : ℤ) ∈ D.p := h613_of_witness W
  let P0 := S2595P0 D h613
  let PT := S2594P P0
  let L := S2595LResidueEquiv D h613
  haveI hpmax : p0.IsMaximal := S2590_contraction_maximal D h613
  haveI hlies : P0.LiesOver p0 := S2595P0_lies D h613
  have hunder : P0.comap (algebraMap S2565ConcreteIntegralClosureCActual.C S2594LP0PActual.OL) = p0 := by
    simpa [Ideal.under, p0] using (S2595P0_lies D h613).over.symm
  haveI : P0.IsMaximal := S2595P0_max D h613
  obtain ⟨k, b, ha⟩ := T_denom_clear a
  have hσa : sigmaRingEquiv sigma a = algebraMap S2594LP0PActual.OL S2594LP0PActual.T (eSigma sigma b) * u ^ k := by
    rw [ha, map_mul, map_pow, sigmaRingEquiv_apply_algebraMap, sigmaRingEquiv_u]
  have hLmk : L (Ideal.Quotient.mk P0 (eSigma sigma b)) =
      Ideal.Quotient.mk PT (algebraMap S2594LP0PActual.OL S2594LP0PActual.T (eSigma sigma b)) :=
    S2595LResidueEquiv_mk_algebraMap D h613 (eSigma sigma b)
  have hLmk0 : L (Ideal.Quotient.mk P0 b) =
      Ideal.Quotient.mk PT (algebraMap S2594LP0PActual.OL S2594LP0PActual.T b) :=
    S2595LResidueEquiv_mk_algebraMap D h613 b
  have hs : Ideal.Quotient.mk P0 (eSigma sigma b) = (Ideal.Quotient.mk P0 b) ^ 613 := by
    have h := s2382_arithFrobAt_reduction (K:=S1720Field) (L:=S2057FiveDivisionField)
      (p:=p0) (P:=P0) sigma H b
    change Ideal.Quotient.mk P0 (sigma • b) =
      (Ideal.Quotient.mk P0 b) ^ Nat.card (S2565ConcreteIntegralClosureCActual.C ⧸ p0) at h
    rw [card_C_quot_p0 W hirr] at h
    simpa [eSigma] using h
  have hu : (Ideal.Quotient.mk PT S2596cDenomClearActual.u) ^ (k * 613) =
      (Ideal.Quotient.mk PT S2596cDenomClearActual.u) ^ k := by
    rw [show k * 613 = 613 * k by ring, pow_mul, u_pow_613 W hirr]
  calc Ideal.Quotient.mk PT (sigmaRingEquiv sigma a)
      = Ideal.Quotient.mk PT (algebraMap S2594LP0PActual.OL S2594LP0PActual.T (eSigma sigma b)) *
          (Ideal.Quotient.mk PT S2596cDenomClearActual.u) ^ k := by
        rw [hσa, map_mul, map_pow]
    _ = (L (Ideal.Quotient.mk P0 (eSigma sigma b))) *
          (Ideal.Quotient.mk PT S2596cDenomClearActual.u) ^ k := by rw [← hLmk]
    _ = (L ((Ideal.Quotient.mk P0 b) ^ 613)) *
          (Ideal.Quotient.mk PT S2596cDenomClearActual.u) ^ k := by rw [← hs]
    _ = (L (Ideal.Quotient.mk P0 b)) ^ 613 *
          (Ideal.Quotient.mk PT S2596cDenomClearActual.u) ^ k := by rw [map_pow]
    _ = (Ideal.Quotient.mk PT (algebraMap S2594LP0PActual.OL S2594LP0PActual.T b)) ^ 613 *
          (Ideal.Quotient.mk PT S2596cDenomClearActual.u) ^ k := by rw [hLmk0]
    _ = frobBar (p := D.p) (P := PT)
          (Ideal.Quotient.mk PT a) := by
        rw [ha, map_mul, map_pow, frobBar, card_S_quot_D W hirr]
        rw [mul_pow, ← pow_mul, hu]
#print axioms localized_reduction_W
end LeanFormal.IUT.XiFPaper.S2596pReductionActual
end
