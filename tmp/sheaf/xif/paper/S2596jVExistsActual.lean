import tmp.sheaf.xif.paper.S2596iResidueNatActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596jVExistsActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2595LResidueEquivActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2596gResidueCompatActual
open LeanFormal.IUT.XiFPaper.S2596iResidueNatActual
open LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual
open LeanFormal.IUT.XiFPaper.S2596dHfixActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
lemma exists_v_residue_u
    (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S2565ConcreteIntegralClosureCActual.S) (613 : ℤ) ∈ D.p) :
    ∃ v : S2594LP0PActual.OL,
      Ideal.Quotient.mk (S2595P0 D h613) v *
        Ideal.Quotient.mk (S2595P0 D h613) S2596cDenomClearActual.aOL = 1 := by
  haveI hmax : (S2595P0 D h613).IsMaximal := S2595P0_max D h613
  have hnot : S2596cDenomClearActual.aOL ∉ S2595P0 D h613 :=
    S2595_Cden_not_mem_P0 D h613
  let J : Ideal S2594LP0PActual.OL := S2595P0 D h613 ⊔ Ideal.span {S2596cDenomClearActual.aOL}
  have haJ : S2596cDenomClearActual.aOL ∈ J :=
    Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hle : S2595P0 D h613 ≤ J := le_sup_left
  have h1 : (1 : S2594LP0PActual.OL) ∈ J :=
    (Ideal.isMaximal_iff.mp hmax).2 J S2596cDenomClearActual.aOL hle hnot haJ
  rw [Submodule.mem_sup] at h1
  obtain ⟨p, hp, z, hz, hpz⟩ := h1
  rw [Ideal.mem_span_singleton] at hz
  obtain ⟨b, hb⟩ := hz
  refine ⟨b, ?_⟩
  have hzq : Ideal.Quotient.mk (S2595P0 D h613) z = 1 := by
    have h := congrArg (Ideal.Quotient.mk (S2595P0 D h613)) hpz
    rw [map_add, map_one] at h
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hp, zero_add] at h
    exact h
  rw [hb, map_mul] at hzq
  rw [mul_comm]
  exact hzq
#print axioms exists_v_residue_u
end LeanFormal.IUT.XiFPaper.S2596jVExistsActual
end
