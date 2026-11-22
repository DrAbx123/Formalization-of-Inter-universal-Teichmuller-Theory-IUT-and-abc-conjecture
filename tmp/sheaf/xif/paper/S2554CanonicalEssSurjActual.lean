import tmp.sheaf.xif.paper.S2541EssSurjAuditActual
import tmp.sheaf.xif.paper.S2519InvEquivalenceGoalActual
import tmp.sheaf.xif.paper.S2517InvObjActual
import tmp.sheaf.xif.paper.S2547TransportIsoActual
import tmp.sheaf.xif.paper.S2521RepresentableStackActual

noncomputable section
open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2519InvEquivalenceGoalActual
open LeanFormal.IUT.XiFPaper.S2541EssSurjAuditActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual

/-- The canonical scheme map underlying a representable cover. -/
noncomputable def S2554CanonicalMap
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S) :
    S ⟶ S2482AffineOver :=
  let m0 : Pseudofunctor.StrongTrans (S2517TStack S).fiber S2482Orbicurve.stack.fiber :=
    hS.symm ▸ X.map
  let m1 : Pseudofunctor.StrongTrans (S2517TStack S).fiber
      (S1742YS (F := F) S2482AffineOver) :=
    (show S2482Orbicurve.stack.fiber = S1742YS (F := F) S2482AffineOver from rfl) ▸ m0
  S1742HomOfStrongTrans (F := F) (S := S) (T := S2482AffineOver) m1

/-- The canonical affine finite etale cover data (conditional on the
finite-etale extraction for the canonical map). -/
structure S2554CanonicalData
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S) where
  etale : Etale (S2554CanonicalMap X S hS).left
  finite : IsFinite (S2554CanonicalMap X S hS).left

/-- The canonical cover C0. -/
noncomputable def S2554CanonicalCover
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S)
    (D : S2554CanonicalData X S hS) :
    FiniteEtaleCover S2482AffineScheme :=
  FiniteEtaleCover.mk (S2554CanonicalMap X S hS).left D.etale D.finite

/-- The representable canonical essential-surjectivity target. -/
def S2554CanonicalEssSurj : Prop :=
  ∀ (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S),
    Nonempty (S2554CanonicalData X S hS) →
      ∃ C : FiniteEtaleCover S2482AffineScheme,
        Nonempty (S2517InvObj C ≅ X)

#check S2554CanonicalMap
#check S2554CanonicalCover
#check S2554CanonicalEssSurj

end LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
end
