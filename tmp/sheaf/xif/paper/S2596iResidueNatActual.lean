import tmp.sheaf.xif.paper.S2596hQuotientCardActual
import tmp.sheaf.xif.paper.S2596gResidueCompatActual
import tmp.sheaf.xif.paper.S2382ArithFrobDoneActual
import tmp.sheaf.xif.paper.S2540AbstractPermBarActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596iResidueNatActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2595LResidueEquivActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2596gResidueCompatActual
open LeanFormal.IUT.XiFPaper.S2596hQuotientCardActual
open LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual
open LeanFormal.IUT.XiFPaper.S2596dHfixActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
local instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) S2594LP0PActual.OL :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers S1720Field) S1720Field S2057FiveDivisionField (RingOfIntegers S2057FiveDivisionField)
lemma frobBar_natural
    (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S2565ConcreteIntegralClosureCActual.S) (613 : ℤ) ∈ D.p)
    (x : S2594LP0PActual.OL ⧸ S2595P0 D h613) :
    S2595LResidueEquiv D h613
        (frobBar (p := D.p.comap (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S))
          (P := S2595P0 D h613) x) =
      frobBar (p := D.p) (P := S2594P (S2595P0 D h613))
        (S2595LResidueEquiv D h613 x) := by
  rw [frobBar, frobBar, map_pow]
  congr 1
  exact (localized_quotient_card D h613).symm
lemma S2595LResidueEquiv_u
    (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S2565ConcreteIntegralClosureCActual.S) (613 : ℤ) ∈ D.p)
    (v : S2594LP0PActual.OL)
    (hv : Ideal.Quotient.mk (S2595P0 D h613) v *
        Ideal.Quotient.mk (S2595P0 D h613) S2596cDenomClearActual.aOL = 1) :
    S2595LResidueEquiv D h613 (Ideal.Quotient.mk (S2595P0 D h613) v) =
      Ideal.Quotient.mk (S2594P (S2595P0 D h613)) S2596cDenomClearActual.u := by
  let yT : S2594LP0PActual.T ⧸ S2594P (S2595P0 D h613) :=
    S2595LResidueEquiv D h613
      (Ideal.Quotient.mk (S2595P0 D h613) S2596cDenomClearActual.aOL)
  have hL : S2595LResidueEquiv D h613
      (Ideal.Quotient.mk (S2595P0 D h613) v) * yT = 1 := by
    rw [← map_mul, hv, map_one]
  have hyT_eq : yT = Ideal.Quotient.mk (S2594P (S2595P0 D h613))
      (algebraMap S2594LP0PActual.OL S2594LP0PActual.T S2596cDenomClearActual.aOL) :=
    S2595LResidueEquiv_mk_algebraMap D h613 S2596cDenomClearActual.aOL
  have hyunit : IsUnit yT :=
    ⟨⟨yT, S2595LResidueEquiv D h613 (Ideal.Quotient.mk (S2595P0 D h613) v),
      by rw [mul_comm]; exact hL, hL⟩, rfl⟩
  have huT : Ideal.Quotient.mk (S2594P (S2595P0 D h613)) S2596cDenomClearActual.u * yT = 1 := by
    rw [hyT_eq, ← map_mul]
    rw [mul_comm S2596cDenomClearActual.u
      (algebraMap S2594LP0PActual.OL S2594LP0PActual.T S2596cDenomClearActual.aOL)]
    exact congrArg (Ideal.Quotient.mk (S2594P (S2595P0 D h613)))
      (by rw [S2596cDenomClearActual.hu])
  exact IsUnit.mul_right_cancel hyunit (hL.trans huT.symm)
#print axioms frobBar_natural
#print axioms S2595LResidueEquiv_u
end LeanFormal.IUT.XiFPaper.S2596iResidueNatActual
end
