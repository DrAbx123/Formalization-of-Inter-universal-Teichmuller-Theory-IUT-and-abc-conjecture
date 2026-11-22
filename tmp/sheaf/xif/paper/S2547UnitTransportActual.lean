/-
# S2547: unit/counit alignment -- full and faithful for S2519InvFunctor

S2538AffineCoverEquiv is the affine cover/algebra equivalence

  E : FiniteEtaleCover S2482AffineScheme ≌ (CommAlgCat.FiniteEtale S2482CoordinateRing)^op,

with unit E.unitIso : 𝟭 _ ≅ E.functor ⋙ E.inverse.  The corrected algebra-side
functor is S2540Functor = E.inverse ⋙ S2519InvFunctor (S2540CorrectedObjectMapActual),
so the unit of E gives a natural isomorphism

  S2547UnitIso : E.functor ⋙ S2540Functor ≅ S2519InvFunctor.

Its component at an affine cover C is the S2519InvFunctor-image of the unit
C ≅ E.inverse.obj (E.functor.obj C); this is exactly the map that transports a
cover map S2517InvObj C ⟶ S2517InvObj D into a map between the inverse images
E.inverse.obj (E.functor.obj C) and E.inverse.obj (E.functor.obj D).

Consequently the already established

* S2542Functor_faithful : S2540Functor.Faithful (S2542FunctorFaithfulActual), and
* S2546FunctorFull : S2540Functor.Full (S2546FunctorFullActual),

compose with the full/faithful functor E.functor and transport along the unit
isomorphism S2547UnitIso to give

* S2547InvFunctorFull : S2519InvFunctor.Full, and
* S2547InvFunctorFaithful : S2519InvFunctor.Faithful,

on the whole category of affine finite etale covers.  No hypothesis is left over:
both statements are unconditional.

No sorry, no new axiom, no native_decide.
-/
import tmp.sheaf.xif.paper.S2519InvFunctorActual
import tmp.sheaf.xif.paper.S2538AffineCoverEquivActual
import tmp.sheaf.xif.paper.S2540CorrectedObjectMapActual
import tmp.sheaf.xif.paper.S2542FunctorFaithfulActual
import tmp.sheaf.xif.paper.S2546FunctorFullActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.XiFPaper.S2542FunctorFaithfulActual
open LeanFormal.IUT.XiFPaper.S2546FunctorFullActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2547UnitTransportActual

/-! ## 1. The unit isomorphism E.functor ⋙ S2540Functor ≅ S2519InvFunctor -/

/-- The unit of the affine cover equivalence, pushed through S2519InvFunctor.

Since S2540Functor = E.inverse ⋙ S2519InvFunctor is definitionally
E.functor ⋙ (E.inverse ⋙ S2519InvFunctor), the inverse of the unit
E.unitIso : 𝟭 _ ≅ E.functor ⋙ E.inverse (whiskered on the right by
S2519InvFunctor) identifies the composite E.functor ⋙ S2540Functor with
S2519InvFunctor.  The only structural isomorphisms involved are the
associator and the left unitor. -/
noncomputable def S2547UnitIso :
    (S2538AffineCoverEquiv.functor ⋙ S2540Functor) ≅ S2519InvFunctor :=
  (Functor.associator S2538AffineCoverEquiv.functor S2538AffineCoverEquiv.inverse
      S2519InvFunctor).symm.trans
    ((Functor.isoWhiskerRight S2538AffineCoverEquiv.unitIso.symm S2519InvFunctor).trans
      (Functor.leftUnitor S2519InvFunctor))

/-- Objectwise form of the transport: for every affine finite etale cover C the
unit C ≅ E.inverse.obj (E.functor.obj C) becomes, after applying
S2519InvFunctor, an isomorphism from S2517InvObj C to the inverse image
S2540Functor.obj (E.functor.obj C). -/
noncomputable def S2547UnitApp (C : FiniteEtaleCover S2482AffineScheme) :
    S2519InvFunctor.obj C ≅
      S2540Functor.obj (S2538AffineCoverEquiv.functor.obj C) :=
  S2519InvFunctor.mapIso (S2538AffineCoverEquiv.unitIso.app C)

/-! ## 2. Fullness -/

/-- S2519InvFunctor is full: E.functor is full (it is the functor of an
equivalence), S2540Functor is full by S2546FunctorFull, hence the composite
E.functor ⋙ S2540Functor is full, and fullness transports along the natural
isomorphism S2547UnitIso given by the unit of E. -/
theorem S2547InvFunctorFull : S2519InvFunctor.Full := by
  letI : S2540Functor.Full := S2546FunctorFull
  exact Functor.Full.of_iso S2547UnitIso

/-! ## 3. Faithfulness -/

/-- S2519InvFunctor is faithful: E.functor is faithful (it is the functor of an
equivalence), S2540Functor is faithful by S2542Functor_faithful, hence
E.functor ⋙ S2540Functor is faithful, and faithfulness transports along the
unit isomorphism S2547UnitIso. -/
theorem S2547InvFunctorFaithful : S2519InvFunctor.Faithful := by
  letI : S2540Functor.Faithful := S2542Functor_faithful
  exact Functor.Faithful.of_iso S2547UnitIso

/-! ## 4. Assembly: the functor is fully faithful -/

/-- The unit/counit alignment yields a fully faithful S2519InvFunctor, i.e. an
actual FullyFaithful structure on the whole category of affine covers. -/
noncomputable def S2547InvFunctorFullyFaithful : S2519InvFunctor.FullyFaithful :=
  letI : S2519InvFunctor.Full := S2547InvFunctorFull
  letI : S2519InvFunctor.Faithful := S2547InvFunctorFaithful
  Functor.FullyFaithful.ofFullyFaithful S2519InvFunctor

/-- The map_surjective content of S2547InvFunctorFull, in the exact form of the
transport: every cover map between S2517InvObj C and S2517InvObj D has a
preimage f : C ⟶ D on affine covers. -/
theorem S2547FullPreimage {C D : FiniteEtaleCover S2482AffineScheme}
    (h : S2519InvFunctor.obj C ⟶ S2519InvFunctor.obj D) :
    ∃ f : C ⟶ D, S2519InvFunctor.map f = h :=
  S2547InvFunctorFull.map_surjective h

/-! ## 5. Checks and axiom audit -/

#check @S2547UnitIso
#check @S2547UnitApp
#check @S2547InvFunctorFull
#check @S2547InvFunctorFaithful
#check @S2547InvFunctorFullyFaithful
#check @S2547FullPreimage

#print axioms S2547UnitIso
#print axioms S2547InvFunctorFull
#print axioms S2547InvFunctorFaithful
#print axioms S2547InvFunctorFullyFaithful
#print axioms S2547FullPreimage

end LeanFormal.IUT.XiFPaper.S2547UnitTransportActual
end
