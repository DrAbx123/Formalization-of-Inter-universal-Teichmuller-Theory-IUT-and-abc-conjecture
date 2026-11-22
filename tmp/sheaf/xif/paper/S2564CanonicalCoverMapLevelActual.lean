import tmp.sheaf.xif.paper.S2562CorrectedEssSurjLiftUniqueActual
import tmp.sheaf.xif.paper.S2554CanonicalEssSurjActual
import tmp.sheaf.xif.paper.S2517InvObjActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2519InvEquivalenceGoalActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2562CorrectedEssSurjLiftUniqueActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2564CanonicalCoverMapLevelActual

/-- The scheme of the canonical cover is `S`. -/
theorem S2564CanonicalCover_source_eq
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S)
    (D : S2554CanonicalData X S hS) :
    (S2517InvObj (S2554CanonicalCover X S hS D)).source = X.source := by
  calc
    (S2517InvObj (S2554CanonicalCover X S hS D)).source
        = S2517TStack (S2517CScheme (S2554CanonicalCover X S hS D)) := rfl
    _ = S2517TStack S := by rw [S2562CanonicalCover_scheme]
    _ = X.source := hS.symm

/-- Map-level form of the canonical-cover identification: after casting the
source, the canonical cover map and `X.map` are 2-isomorphic. -/
def S2564CanonicalCoverMapLevel
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F)
    (hS : X.source = S2517TStack S)
    (D : S2554CanonicalData X S hS) : Prop := by
  let C0 := S2554CanonicalCover X S hS D
  let A := S2517InvObj C0
  let hsrc : A.source = X.source := S2564CanonicalCover_source_eq X S hS D
  exact Nonempty (Iso (hsrc ▸ A.map) X.map)

#check S2564CanonicalCover_source_eq
#check S2564CanonicalCoverMapLevel
#print axioms S2564CanonicalCover_source_eq
end LeanFormal.IUT.XiFPaper.S2564CanonicalCoverMapLevelActual
end