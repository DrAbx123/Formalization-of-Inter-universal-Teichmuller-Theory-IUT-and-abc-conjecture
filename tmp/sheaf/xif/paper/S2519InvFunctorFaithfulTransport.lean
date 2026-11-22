import tmp.sheaf.xif.paper.S2519InvFunctorActual
import tmp.sheaf.xif.paper.S2538AffineCoverEquivActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2519InvFunctorFaithfulTransport

/-- A retraction of the inverse functor on hom sets. -/
def S2519InvFunctorFaithfulRetraction : Prop :=
  ∃ retr : ∀ {C D : FiniteEtaleCover S2482AffineScheme},
      (S2517InvObj C ⟶ S2517InvObj D) → (C ⟶ D),
    ∀ {C D : FiniteEtaleCover S2482AffineScheme} (f : C ⟶ D),
      retr (S2519InvFunctor.map f) = f

/-- Faithful follows from a hom-level retraction. -/
theorem S2519InvFunctor_faithful_of_retraction
    (h : S2519InvFunctorFaithfulRetraction) :
    S2519InvFunctor.Faithful := by
  rcases h with ⟨retr, hretr⟩
  refine { map_injective := ?_ }
  intro C D f g hfg
  calc
    f = retr (S2519InvFunctor.map f) := (hretr f).symm
    _ = retr (S2519InvFunctor.map g) := by rw [hfg]
    _ = g := hretr g

#check S2519InvFunctorFaithfulRetraction
#check S2519InvFunctor_faithful_of_retraction

end LeanFormal.IUT.XiFPaper.S2519InvFunctorFaithfulTransport
end
