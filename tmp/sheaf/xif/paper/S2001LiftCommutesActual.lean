import tmp.sheaf.xif.paper.S1985SiteLiftNaturalityActual

/-!
# S2001: the site-level lift commutation for the pseudopullback

This file supplies the "liftCommutes" part of the remaining site-level (d)
data of S1985ApexData, and records the exact first missing input for "uniq".

## What is proved

For every cospan of actual finite-etale cover maps f : A -> C, g : B -> C,
every cover W and every bicone c : S1832Bicone f g W, the constructed
site-level lift liftSite c is compatible with the chosen structure map:

  liftCommutes : Iso (vcomp (liftSite c) (structureMap f g)) W.map .

The proof is the honest composition of three actual 2-isomorphisms:

1. the bicategory associator (liftSite c ≫ toA f g) ≫ A.map ≅
   liftSite c ≫ (toA f g ≫ A.map) from Bicategory.associator;
2. the right whiskering of liftToA c : liftSite c ≫ toA f g ≅ c.toA.map
   with A.map from Bicategory.whiskerRightIso;
3. the first-leg compatibility c.toA.commutes : (c.toA.map ≫ A.map) ≅ W.map.

The instance-coherence obstruction between EtaleStackPseudofunctor.homCategory
and the scoped Pseudofunctor.StrongTrans.homCategory is bypassed by passing
the bicategory instance explicitly to Bicategory.associator and
Bicategory.whiskerRightIso. No 2-cell is fabricated: every component is one
of the already constructed isomorphisms, and the only axioms used are
propext, Classical.choice and Quot.sound.

## The precise first missing input for uniq

"uniq" in S1985ApexData asks, for every
h : W.source.fiber -> sitePseudofunctor f g with
h ≫ structureMap ≅ W.map, that isomorphisms of the two legs
h ≫ toA ≅ c.toA.map and h ≫ toB ≅ c.toB.map imply
Nonempty (Iso h (liftSite c)).

Those hypotheses do not imply the conclusion in a general 2-category. The
site iso-comma is the pointwise iso-comma of f.map and g.map; already for

* A = B = 1 the terminal category,
* C = BG the one-object category with Aut(*) = Z/2,
* L = R : 1 -> BG the unique functor,

the site iso-comma IsoComma L R is the discrete category on Z/2. Taking
W = 1 and c with c.toA = c.toB = ! and c.commutes = 1, the lifts h = 1 and
liftSite c = sigma have the same (hence isomorphic) legs to A and B, and
satisfy the hmap condition, but they are not isomorphic in IsoComma L R.
The missing datum is exactly the compatibility 2-cell of a morphism of cones
(the ConeMorphism.compatibility field of the finite-etale base-change datum),
which is not among the hypotheses of uniq.

In the intended geometry this coherence is expected to be automatic because
every finite-etale cover is representable by a scheme/algebraic space, so its
fibre categories are 0-truncated (all hom types are subsingletons). That
truncation is recorded below as S2001CoverFiberDiscrete; it is not derived
from the current EtaleStackFiniteEtaleMorphism data in the tree, and its
global form S2001UniqFirstMissing is the exact first missing statement.

Once the 0-truncation is available, the obstruction disappears: the
iso-comma square condition becomes a subsingleton equality, as recorded in
siteIsoComma_square_automatic. The remaining work for uniq is therefore only
the bookkeeping of the modification components, not a missing 2-cell.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S1985SiteLiftNaturalityActual
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace LeanFormal.IUT.XiFPaper.S2001LiftCommutesActual

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- **The site-level commutation of the lift with the structure map** (field
liftCommutes of S1985ApexData). The domain is the composition of the lift
with the chosen structure map structureMap f g (definitionally
vcomp (toA f g) A.map); the codomain is the structure map W.map of the test
cover. The three 2-isomorphisms are the bicategory associator, the whiskered
liftToA, and the first leg of the bicone. -/
noncomputable def liftCommutes (W : S1728Cover) (c : S1832Bicone f g W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (liftSite (f := f) (g := g) c)
      (structureMap f g)) W.map :=
  (@Bicategory.associator
    (Pseudofunctor (CategoryTheory.LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
      CategoryTheory.Cat) inferInstance
    W.source.fiber (sitePseudofunctor f g) A.source.fiber
    S1726Orbicurve.stack.fiber
    (liftSite (f := f) (g := g) c) (toA f g) A.map).symm.trans
  (@Bicategory.whiskerRightIso
    (Pseudofunctor (CategoryTheory.LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
      CategoryTheory.Cat) inferInstance
    W.source.fiber A.source.fiber S1726Orbicurve.stack.fiber
    (Pseudofunctor.StrongTrans.vcomp (liftSite (f := f) (g := g) c) (toA f g))
    c.toA.map
    (liftToA (f := f) (g := g) c) A.map) |>.trans c.toA.commutes

/-- The precise missing input for uniq: the fibre categories of a cover C are
0-truncated. This is expected to follow from the representable finite-etale
condition (every base change of C.map is a scheme), but that
representability/descent step is not formalized in the tree. -/
def S2001CoverFiberDiscrete (C : S1728Cover) : Prop :=
  forall (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (X Y : ↑(C.source.fiber.obj U)), Subsingleton (X ⟶ Y)

/-- Under the missing 0-truncation input, the square condition of the site
iso-comma is automatic. This is exactly the coherence that is absent from the
hypotheses of uniq; with it, every pair of comparison morphisms of the two
projections is a morphism of the iso-comma. -/
theorem siteIsoComma_square_automatic (hC : S2001CoverFiberDiscrete C)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    {X Y : S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor}
    (u : (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).obj X ⟶
      (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).obj Y)
    (v : (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).obj X ⟶
      (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).obj Y) :
    (f.map.app U).toFunctor.map u ≫ Y.obj.hom =
      X.obj.hom ≫ (g.map.app U).toFunctor.map v := by
  haveI : Subsingleton
      ((f.map.app U).toFunctor.obj
          ((S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).obj X) ⟶
        (g.map.app U).toFunctor.obj Y.obj.right) :=
    hC U _ _
  exact Subsingleton.elim _ _

/-- **The exact first missing statement for uniq**: every actual
finite-etale cover has discrete (0-truncated) fibre categories. Under this
input the cone coherence of uniq is automatic, because the iso-comma square
condition lives in a subsingleton hom type; without it uniq fails already in
the abstract 2-category Cat (counterexample in the module docstring). -/
def S2001UniqFirstMissing : Prop := forall C : S1728Cover, S2001CoverFiberDiscrete C

/-! ## Checks and axiom audit -/

#check liftCommutes
#check S2001CoverFiberDiscrete
#check siteIsoComma_square_automatic
#check S2001UniqFirstMissing

#print axioms liftCommutes
#print axioms S2001CoverFiberDiscrete
#print axioms siteIsoComma_square_automatic
#print axioms S2001UniqFirstMissing

end LeanFormal.IUT.XiFPaper.S2001LiftCommutesActual
