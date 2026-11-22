import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind2Reduction

/-! # Mzk1Ind2DescentConsumerGlueActual — consumer forms of the (Ind1)/(Ind2) descent

Small reference/glue module (no new mathematics): derives the mixed-step invariance and
the representative-level consequence of the already-proved second-link descent
(`secondLinkDescent_ind1Step`, `secondLinkDescent_ind2Step`,
`secondLinkDescent_eq_lift`, `linkMap_respects_indeterminacy`).  These are the forms
consumed by the Theorem 3.11 object layer ("regarded up to Ind1, Ind2").
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Ind2DescentConsumerGlueActual

open LeanFormal.IUT
open MultiradialKernel

universe u v

variable {LabelNative LabelAlien : Type u} {Native Alien : Type v}
  [AddGroup LabelNative] [AddGroup LabelAlien]

/-- Mixed invariance: a native (Ind1)-step followed by an (Ind2)-step is invisible
to the descended second link. -/
theorem secondLinkDescent_ind1_ind2 (D : Ind2AlienLink LabelNative LabelAlien Native Alien)
    (g₁ g₂ : LabelNative) (a : Native) :
    D.secondLinkDescent
        (Quotient.mk'' (D.nativeCore.ind1 g₁ (D.nativeCore.ind2 g₂ a))) =
      D.secondLinkDescent (Quotient.mk'' a) := by
  rw [D.secondLinkDescent_ind1Step g₁ (D.nativeCore.ind2 g₂ a),
    D.secondLinkDescent_ind2Step g₂ a]

/-- Mixed invariance in the other order. -/
theorem secondLinkDescent_ind2_ind1 (D : Ind2AlienLink LabelNative LabelAlien Native Alien)
    (g₁ g₂ : LabelNative) (a : Native) :
    D.secondLinkDescent
        (Quotient.mk'' (D.nativeCore.ind2 g₁ (D.nativeCore.ind1 g₂ a))) =
      D.secondLinkDescent (Quotient.mk'' a) := by
  rw [D.secondLinkDescent_ind2Step g₁ (D.nativeCore.ind1 g₂ a),
    D.secondLinkDescent_ind1Step g₂ a]

/-- The descent evaluated through the generic quotient-compatible lift. -/
theorem secondLinkDescent_apply_eq_lift
    (D : Ind2AlienLink LabelNative LabelAlien Native Alien)
    (q : Core.GeneratedQuotient D.nativeCore) :
    D.secondLinkDescent q = D.asQuotientCompatibleMap.lift q := by
  rw [D.secondLinkDescent_eq_lift]

/-- Representative-level consequence: the (Ind1)/(Ind2)-generated equality is mapped
to an equality of the descended classes. -/
theorem linkMap_generated_eq
    (D : Ind2AlienLink LabelNative LabelAlien Native Alien) {a b : Native}
    (h : Core.GeneratedEqualityRelation D.nativeCore a b) :
    (Quotient.mk'' (s₁ := Core.generatedSetoid D.alienCore) (D.linkMap a)) =
      (Quotient.mk'' (s₁ := Core.generatedSetoid D.alienCore) (D.linkMap b)) := by
  rw [← D.secondLinkDescent_mk, ← D.secondLinkDescent_mk]
  exact Quotient.sound (D.linkMap_respects_indeterminacy h)

#check secondLinkDescent_ind1_ind2
#check secondLinkDescent_ind2_ind1
#check secondLinkDescent_apply_eq_lift
#check linkMap_generated_eq

end LeanFormal.IUT.XiFPaper.Mzk1Ind2DescentConsumerGlueActual
end
