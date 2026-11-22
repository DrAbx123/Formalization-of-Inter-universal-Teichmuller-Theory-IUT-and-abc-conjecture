import tmp.sheaf.xif.paper.S2226TransferProductActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2233TransferProductProofActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2215TransversalTransportActual
open LeanFormal.IUT.XiFPaper.S2226TransferProductActual

universe u

/-- Left-coset quotient reindexing along a multiplicative equivalence. -/
noncomputable def S2233LeftCosetReindex {G G' : Type u} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) :
    Quotient (QuotientGroup.leftRel H) ≃
      Quotient (QuotientGroup.leftRel (H.map e.toMonoidHom)) where
  toFun := Quotient.map (e : G → G') (by
    intro a b hab
    exact QuotientGroup.leftRel_apply.mpr (by
      have hmem : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
      simpa [map_mul] using
        (Subgroup.mem_map_of_mem e.toMonoidHom hmem)))
  invFun := Quotient.map (e.symm : G' → G) (by
    intro a b hab
    exact QuotientGroup.leftRel_apply.mpr (by
      have hmem : a⁻¹ * b ∈ H.map e.toMonoidHom :=
        QuotientGroup.leftRel_apply.mp hab
      have hpre : e.symm (a⁻¹ * b) ∈ H :=
        (Subgroup.mem_map_equiv (f := e) (K := H)).mp hmem
      simpa [map_mul] using hpre))
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro a
    rw [Quotient.map_mk, Quotient.map_mk]
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by simp))
  right_inv x := by
    refine Quotient.inductionOn x ?_
    intro a
    rw [Quotient.map_mk, Quotient.map_mk]
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by simp))

#check S2233LeftCosetReindex
#print axioms S2233LeftCosetReindex

end LeanFormal.IUT.XiFPaper.S2233TransferProductProofActual

end