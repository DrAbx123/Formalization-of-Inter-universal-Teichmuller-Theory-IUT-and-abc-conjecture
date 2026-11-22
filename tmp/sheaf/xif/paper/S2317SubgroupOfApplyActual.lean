import tmp.sheaf.xif.paper.S2314SubgroupOfMapFinalActual
import tmp.sheaf.xif.paper.S2311OpenComapActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2317SubgroupOfApplyActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2173StageConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual
open LeanFormal.IUT.XiFPaper.S2311OpenComapActual

variable (p : Nat) [Fact (Nat.Prime p)]

theorem S2317ConjEquiv_apply (g : Gv p) (H : Index p) (x : ↥H) :
    ((S2200ConjEquiv p g H x : Gv p)) = g⁻¹ * (x : Gv p) * g := by
  change (MulAut.conj g.symm) (x : Gv p) = g⁻¹ * (x : Gv p) * g
  rw [MulAut.conj_apply]
  change g⁻¹ * ((x : Gv p) * g) = g⁻¹ * ((x : Gv p) * g)
  rfl


theorem S2317_subgroupOf_map (g : Gv p) (H K : Index p) (h : H ≤ K) :
    ((H.toSubgroup.subgroupOf K.toSubgroup).map
        (S2200ConjEquiv p g K).toMonoidHom) =
      (S2169ConjIndex p g H).toSubgroup.subgroupOf
        (S2169ConjIndex p g K).toSubgroup := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxH : (x : Gv p) ∈ H := by
      exact OpenSubgroup.mem_toSubgroup.mpr (Subgroup.mem_subgroupOf.mp hx)
    rw [Subgroup.mem_subgroupOf]
    change (S2200ConjEquiv p g K x : Gv p) ∈
      (H.comap (MulAut.conj g).toMonoidHom
        (IsTopologicalGroup.continuous_conj g) : Subgroup (Gv p))
    rw [S2311_mem_comap_toSubgroup H (MulAut.conj g).toMonoidHom
      (IsTopologicalGroup.continuous_conj g)]
    rw [S2317ConjEquiv_apply]
    convert hxH using 1
    simp [mul_assoc]
  · intro hy
    have hyH : (y : Gv p) ∈ (S2169ConjIndex p g H).toSubgroup :=
      Subgroup.mem_subgroupOf.mp hy
    have hyO : (y : Gv p) ∈ S2169ConjIndex p g H := by
      simpa [OpenSubgroup.mem_toSubgroup] using hyH
    change (y : Gv p) ∈ (H.comap (MulAut.conj g).toMonoidHom
      (IsTopologicalGroup.continuous_conj g) : OpenSubgroup (Gv p)) at hyO
    have hconj : g * (y : Gv p) * g⁻¹ ∈ H :=
      OpenSubgroup.mem_comap.mp hyO
    rw [Subgroup.mem_map]
    refine ⟨(S2200ConjEquiv p g K).symm y, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have hsymm : (((S2200ConjEquiv p g K).symm y : ↥K) : Gv p) =
          g * (y : Gv p) * g⁻¹ := by
        have h := S2317ConjEquiv_apply p g K ((S2200ConjEquiv p g K).symm y)
        have h' : (y : Gv p) = g⁻¹ *
            ↑((S2200ConjEquiv p g K).symm y) * g := by
          simpa [Equiv.apply_symm_apply] using h
        rw [h']
        group
      rw [hsymm]
      exact OpenSubgroup.mem_toSubgroup.mpr hconj
    · exact (S2200ConjEquiv p g K).apply_symm_apply y

#check S2317_subgroupOf_map
#print axioms S2317_subgroupOf_map

#check S2317ConjEquiv_apply
#print axioms S2317ConjEquiv_apply

end LeanFormal.IUT.XiFPaper.S2317SubgroupOfApplyActual

end