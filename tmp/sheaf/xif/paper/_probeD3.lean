import tmp.sheaf.xif.paper.S2543CorrectedQuotMapActual
import tmp.sheaf.xif.paper.S2544D2SchemeMapActual
import tmp.sheaf.xif.paper.S2541CoverHomToAlgActual
import tmp.sheaf.xif.paper.S2537RepresentableModificationActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2518InvCoverMapActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.XiFPaper.S2541CoverHomToAlgActual
open LeanFormal.IUT.XiFPaper.S2543CorrectedQuotMapActual
open LeanFormal.IUT.XiFPaper.S2544D2SchemeMapActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.ProbeD3

#check @Equivalence.unit_app_inverse
#check @Equivalence.unitInv_app_inverse
#check @Equivalence.unit_naturality
#check @Equivalence.unitIso_hom_inv_id_app
#check @Functor.inv_fun_map
#check @Equivalence.counit_naturality

noncomputable abbrev invCover (A : CommAlgCat.FiniteEtale S2482CoordinateRing) :
    FiniteEtaleCover S2482AffineScheme :=
  S2538AffineCoverEquiv.inverse.obj (Opposite.op A)

variable {A B : CommAlgCat.FiniteEtale S2482CoordinateRing}
variable (h0 : Iut.OrbicurveFiniteEtaleCoverMap (S2540ObjectMap B) (S2540ObjectMap A))

example : True := by
  have h := S1742HomOfStrongTrans_congr h0.commutes
  rw [S1742HomOfStrongTrans_vcomp] at h
  trivial

example :
    (S2538AffineCoverEquiv.inverse.map (S2538AffineCoverEquiv.counitIso.app (Opposite.op A)).hom = S2538AffineCoverEquiv.unitInv.app (invCover A)) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    -- this is the actual proof we want
    exact (S2538AffineCoverEquiv.unitInv_app_inverse (Opposite.op A)).symm

end LeanFormal.IUT.XiFPaper.ProbeD3
end
