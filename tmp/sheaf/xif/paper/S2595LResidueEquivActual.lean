import tmp.sheaf.xif.paper.S2594LP0PActual
import tmp.sheaf.xif.paper.S2593ConditionalChainActual
import tmp.sheaf.xif.paper.S2591LocalizedResidueEquivActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2595LResidueEquivActual

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2593ConditionalChainActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual

abbrev OL : Type := NumberField.RingOfIntegers S2057FiveDivisionField

noncomputable def S2595P0 (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S) (613 : ℤ) ∈ D.p) : Ideal OL :=
  Classical.choose (S2593_P0_exists D h613)

lemma S2595P0_max (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S) (613 : ℤ) ∈ D.p) :
    (S2595P0 D h613).IsMaximal :=
  (Classical.choose_spec (S2593_P0_exists D h613)).1

lemma S2595P0_lies (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S) (613 : ℤ) ∈ D.p) :
    (S2595P0 D h613).LiesOver (D.p.comap (algebraMap C S)) :=
  (Classical.choose_spec (S2593_P0_exists D h613)).2

lemma S2595_Cden_not_mem_q (D : S2587LocalizedResidueDataS) :
    (Cden : C) ∉ D.p.comap (algebraMap C S) := by
  intro h
  have hmem : algebraMap C S (Cden : C) ∈ D.p :=
    (Ideal.mem_comap).mp h
  have hmemM : (Cden : C) ∈ Algebra.algebraMapSubmonoid C (Submonoid.powers (c : ℤ)) := by
    refine ⟨(Cden : ℤ), ?_, by simp⟩
    exact (Submonoid.mem_powers_iff (Cden : ℤ) (c : ℤ)).mpr ⟨1, by simp [c]⟩
  have hunit : IsUnit (algebraMap C S (Cden : C)) := by
    exact IsLocalization.map_units S ⟨_, hmemM⟩
  exact D.p_max.ne_top (Ideal.eq_top_of_isUnit_mem (I := D.p) hmem hunit)

lemma S2595_Cden_not_mem_P0 (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S) (613 : ℤ) ∈ D.p) :
    algebraMap C OL (Cden : C) ∉ S2595P0 D h613 := by
  intro h
  have hlies := S2595P0_lies D h613
  have hunder : D.p.comap (algebraMap C S) = (S2595P0 D h613).under C :=
    Ideal.over_def (S2595P0 D h613) (D.p.comap (algebraMap C S))
  have hq : (Cden : C) ∈ D.p.comap (algebraMap C S) := by
    rw [hunder]
    exact (Ideal.mem_comap).mpr h
  exact S2595_Cden_not_mem_q D hq

noncomputable def S2595LResidueEquiv (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S) (613 : ℤ) ∈ D.p) :
    (OL ⧸ S2595P0 D h613) ≃+* (T ⧸ S2594P (S2595P0 D h613)) := by
  haveI : (S2595P0 D h613).IsMaximal := S2595P0_max D h613
  exact S2594LResidueEquiv (S2595P0 D h613) (S2595_Cden_not_mem_P0 D h613)

end LeanFormal.IUT.XiFPaper.S2595LResidueEquivActual
end