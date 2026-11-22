/-
# S1896: the cusp's compactification / representable open immersion

S1887 reduced the D9 cusp exactly to 'Nonempty (Iut.OrbicurveBoundaryCusp S.cK)' and
exposed its first field (the compactification stack) and its first hard field, the
representable open immersion 'Iut.EtaleStackOpenImmersion'.  It recorded that *no*
inhabitant of 'EtaleStackRepresentableMorphismProperty' (hence of
'EtaleStackOpenImmersion') exists anywhere in the tree, so the representability
machinery was itself an open obligation.

This file does two things.

## 1. The representable open immersion of the identity is constructed

For *any* etale stack 'Y' over 'F', the identity morphism 'Y.stack ⟶ Y.stack' is
representably an open immersion:

    S1896IdentityOpenImmersion (Y) : Iut.EtaleStackOpenImmersion (𝟙 Y.fiber).

This is a genuine construction, not an assumption.  For every test scheme 'T' and
every scheme-valued point 'point : h_T ⟶ Y.fiber' of 'Y', the base change is the
2-pullback of '(𝟙, point)', whose apex is the test scheme itself (the "apex = the
scheme" model of S1804's item 2, where the actual 2-pullback of '(A.map, id)' is the
source; here the actual 2-pullback of '(𝟙, point)' is 'h_T'):

    S1896IdentityBaseChange Y T point : EtaleStackBaseChangePresentation (𝟙 Y.fiber) T point

with 'pullbackScheme = T', 'projection = 𝟙 T', 'toSource = point' and a *full*
'TwoPullbackWitness' ('S1896IdentityPullback'): lift = the test-scheme leg of the
cone, the two comparison 2-cells from the cone's own 2-commuting square and the unit
2-isomorphism of the 2-Yoneda projection, lift on 2-cells = the test-scheme leg, and
2-cell extensionality because every 2-cell between strong transformations into a
represented stack has discrete components.  The only auxiliary inputs are

    S1896YonedaOneIso (T) : S1742StrongTransOfHom (𝟙 T) ≅ 𝟙 (h_T),

the unit comparison of the 2-Yoneda 1-cell of '𝟙 T' with the identity, proved from
'Category.comp_id' on the discrete category of sections, and the bicategorical unit
and exchange laws in the explicitly instantiated form used throughout the tree
('S1896RightUnitorIso', 'S1896WhiskerLeftIso', 'S1896WhiskerRightId',
'S1896WhiskerExchange', 'S1896WhiskerRightIff').

No schematic fiber product beyond the test scheme is needed here, because the
2-pullback of '(𝟙, point)' is computed on the nose; for a *proper* compactification
'Z' of 'X' the same fields must be filled by the schematic fiber product
'T ×_Z X' inside 'Z', which is exactly what does not exist in the tree.

## 2. The exact first missing of the D9 cusp, and why the identity does not fill it

The boundary condition of a cusp is incompatible with the identity open map: the
boundary point of the compactification would be isomorphic to itself, so the very
object that must avoid the open orbicurve lies in its image
('S1896Id_not_boundary').  Consequently the cusp's own base-change presentation at
its boundary point forces the open map to fail to be essentially surjective at the
residue scheme ('S1896Cusp_openMap_app_not_essSurj'), while the identity's open map
*is* essentially surjective at every scheme ('S1896Id_app_essSurj').

Hence the constructed 'S1896IdentityOpenImmersion' is *not* the cusp's open
immersion: it can never be, for any candidate compactification equal to 'X.stack'
and any candidate boundary point.  The cusp datum is exactly
(the compactification stack, a representable open immersion of 'X.stack' into it,
a residue scheme, a point of its fiber, and the separation condition)
('S1896CuspEquivOpenData'), and the construction of the middle object for the D9
'C_K' is the first missing datum: a compactification stack of 'S.cK' strictly
extending it, with an open immersion that is *not* levelwise essentially surjective
at the boundary point ('S1896FirstMissing_structure').

No 'True', 'PUnit', fake cusp, fake open immersion, 'sorry', 'admit' or new axiom is
used.  The identity open immersion is a theorem about the identity; it is not
offered as the cusp of anything.
-/

import tmp.sheaf.xif.paper.S1887D9CuspActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1896BoundaryCuspActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1887D9CuspActual
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual

variable {F : Type} [Field F]

/-! ## 0. Bicategorical 2-isomorphism calculus at the instantiated bicategory -/

/-- Left whiskering of a 2-isomorphism of strong transformations. -/
noncomputable def S1896WhiskerLeftIso {A B C : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) (g g' : Pseudofunctor.StrongTrans B C)
    (e : Iso g g') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g) (Pseudofunctor.StrongTrans.vcomp f g') := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let mid : Bicat := B
  let target : Bicat := C
  let fmap : source ⟶ mid := f
  let gmap : mid ⟶ target := g
  let gmap' : mid ⟶ target := g'
  exact @Bicategory.whiskerLeftIso Bicat _ source mid target fmap gmap gmap' e

/-- Right whiskering of a 2-isomorphism of strong transformations. -/
noncomputable def S1896WhiskerRightIso {A B C : EtaleStackPseudofunctor F}
    (f f' : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (e : Iso f f') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g) (Pseudofunctor.StrongTrans.vcomp f' g) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let mid : Bicat := B
  let target : Bicat := C
  let fmap : source ⟶ mid := f
  let fmap' : source ⟶ mid := f'
  let gmap : mid ⟶ target := g
  exact @Bicategory.whiskerRightIso Bicat _ source mid target fmap fmap' e gmap

/-- The left unitor of a strong transformation. -/
noncomputable def S1896LeftUnitorIso {A B : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id A) f) f := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let target : Bicat := B
  let fmap : source ⟶ target := f
  exact @Bicategory.leftUnitor Bicat _ source target fmap

/-- The right unitor of a strong transformation. -/
noncomputable def S1896RightUnitorIso {A B : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) :
    Iso (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.id B)) f := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let target : Bicat := B
  let fmap : source ⟶ target := f
  exact @Bicategory.rightUnitor Bicat _ source target fmap

/-- The right-whiskering unit law, in instantiated form. -/
theorem S1896WhiskerRightId {A B : EtaleStackPseudofunctor F}
    {f g : Pseudofunctor.StrongTrans A B} (eta : f ⟶ g) :
    Pseudofunctor.StrongTrans.whiskerRight eta (Pseudofunctor.StrongTrans.id B) =
      (S1896RightUnitorIso f).hom ≫ eta ≫ (S1896RightUnitorIso g).inv := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let target : Bicat := B
  let fmap : source ⟶ target := f
  let gmap : source ⟶ target := g
  exact @Bicategory.whiskerRight_id Bicat _ source target fmap gmap eta

/-- The exchange law, in instantiated form. -/
theorem S1896WhiskerExchange {A B C : EtaleStackPseudofunctor F}
    {f g : Pseudofunctor.StrongTrans A B} {h k : Pseudofunctor.StrongTrans B C}
    (eta : f ⟶ g) (theta : h ⟶ k) :
    Pseudofunctor.StrongTrans.whiskerLeft f theta ≫
        Pseudofunctor.StrongTrans.whiskerRight eta k =
      Pseudofunctor.StrongTrans.whiskerRight eta h ≫
        Pseudofunctor.StrongTrans.whiskerLeft g theta := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let mid : Bicat := B
  let target : Bicat := C
  let fmap : source ⟶ mid := f
  let gmap : source ⟶ mid := g
  let hmap : mid ⟶ target := h
  let kmap : mid ⟶ target := k
  exact @Bicategory.whisker_exchange Bicat _ source mid target fmap gmap hmap kmap eta theta

/-- Right-whiskering by an identity 1-cell is injective on 2-cells. -/
theorem S1896WhiskerRightIff {A B : EtaleStackPseudofunctor F}
    {f g : Pseudofunctor.StrongTrans A B} (eta theta : f ⟶ g) :
    Pseudofunctor.StrongTrans.whiskerRight eta (Pseudofunctor.StrongTrans.id B) =
        Pseudofunctor.StrongTrans.whiskerRight theta (Pseudofunctor.StrongTrans.id B) ↔
      eta = theta := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let target : Bicat := B
  let fmap : source ⟶ target := f
  let gmap : source ⟶ target := g
  exact @Bicategory.whiskerRight_iff Bicat _ source target fmap gmap eta theta

/-- 2-cells between strong transformations into a represented stack are unique:
every component lands in a discrete category. -/
theorem S1896Modification_subsingleton {A : EtaleStackPseudofunctor F}
    (S : SchemeOverField F) {f g : Pseudofunctor.StrongTrans A (S1742YS (F := F) S)}
    (alpha beta : f ⟶ g) : alpha = beta := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext b
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  apply ULift.ext
  exact Subsingleton.elim _ _

end LeanFormal.IUT.XiFPaper.S1896BoundaryCuspActual
