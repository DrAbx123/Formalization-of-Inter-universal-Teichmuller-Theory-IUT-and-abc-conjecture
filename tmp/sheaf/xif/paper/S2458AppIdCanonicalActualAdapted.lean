import tmp.sheaf.xif.paper.S2456AppEqToIsoActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2456AppEqToIsoActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2458AppIdCanonicalActualAdapted

variable {A B C : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ}
variable (f : A ⟶ B) (g : B ⟶ C)
variable (M : S2152Q.obj A)

theorem S2458_app_id_canonical :
    ((S2152PFunctor.toPseudofunctor'.mapComp' f g (f ≫ g) rfl).hom.toNatTrans.app M) =
      𝟙 ((S2152PFunctor.map (f ≫ g)).toFunctor.obj M) := by
  rw [S2456_app_eq_eqToIso]
  rfl

#print axioms S2458_app_id_canonical

end LeanFormal.IUT.XiFPaper.S2458AppIdCanonicalActualAdapted

end
