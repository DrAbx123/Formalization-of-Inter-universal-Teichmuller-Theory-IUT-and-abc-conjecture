import tmp.sheaf.xif.paper.S2517InvObjActual
import tmp.sheaf.xif.paper.S2517CoverEquivObjectActual
import tmp.sheaf.xif.paper.S2521RepresentableStackActual
import tmp.sheaf.xif.paper.S2517RepresentableFiniteEtaleActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivObjectActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2541EssSurjAuditActual

/-- A cover is representable when its source stack is a representable etale
stack of a scheme over F. -/
def S2541Representable (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) : Prop :=
  ∃ S : Iut.SchemeOverField F, X.source = S2517TStack S

/-- Every object in the image of `S2517InvObj` is representable: its source
is by construction `S2517TStack (S2517CScheme C)`. -/
theorem S2541InvObjRepresentable
    (C : FiniteEtaleCover S2482AffineScheme) :
    S2541Representable (S2517InvObj C) :=
  ⟨S2517CScheme C, rfl⟩

/-- Essential surjectivity of the inverse functor on all covers. -/
def S2541EssSurjAll : Prop :=
  ∀ X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve,
    ∃ C : FiniteEtaleCover S2482AffineScheme, S2517InvObj C = X

/-- Audit: essential surjectivity on all covers would force every orbicurve
cover to be representable. -/
theorem S2541EssSurjAll_implies_representable
    (h : S2541EssSurjAll) :
    ∀ X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve,
      S2541Representable X := by
  intro X
  rcases h X with ⟨C, rfl⟩
  exact S2541InvObjRepresentable C

/-- The restricted essential surjectivity target: every representable cover
is in the image. -/
def S2541EssSurjOnRepresentable : Prop :=
  ∀ X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve,
    S2541Representable X →
      ∃ C : FiniteEtaleCover S2482AffineScheme, S2517InvObj C = X

#check S2541Representable
#check S2541InvObjRepresentable
#check S2541EssSurjAll_implies_representable
#check S2541EssSurjOnRepresentable
#print axioms S2541InvObjRepresentable
#print axioms S2541EssSurjAll_implies_representable
end LeanFormal.IUT.XiFPaper.S2541EssSurjAuditActual
end