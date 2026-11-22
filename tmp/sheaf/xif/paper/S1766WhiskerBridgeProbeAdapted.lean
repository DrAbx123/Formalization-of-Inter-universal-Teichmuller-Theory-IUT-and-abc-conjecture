import tmp.sheaf.xif.paper.S1763HomVcompActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1766WhiskerBridgeProbeAdapted

noncomputable def S1766_whiskerRightIso_vcomp
    {X Y Z : EtaleStackPseudofunctor S1726K}
    (f g : X ⟶ Y) (e : f ≅ g) (h : Y ⟶ Z) :
    Iso (Pseudofunctor.StrongTrans.vcomp f h)
        (Pseudofunctor.StrongTrans.vcomp g h) := by
  change Iso (f ≫ h) (g ≫ h)
  exact Bicategory.whiskerRightIso e h

#print axioms S1766_whiskerRightIso_vcomp

end LeanFormal.IUT.XiFPaper.S1766WhiskerBridgeProbeAdapted
end
