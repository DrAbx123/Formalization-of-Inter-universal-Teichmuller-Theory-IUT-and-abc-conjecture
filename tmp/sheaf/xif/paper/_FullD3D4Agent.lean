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
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.FullD3D4Agent

/-- The affine cover attached to a finite etale algebra by the S2538 equivalence. -/
noncomputable abbrev invCover (A : CommAlgCat.FiniteEtale S2482CoordinateRing) :
    FiniteEtaleCover S2482AffineScheme :=
  S2538AffineCoverEquiv.inverse.obj (Opposite.op A)

variable {A B : CommAlgCat.FiniteEtale S2482CoordinateRing}

/-- The compatibility of the base map with the structure morphisms over
S2482AffineScheme, extracted from the commuting 2-cell of the cover map. -/
theorem coverHomOf_w
    (h0 : Iut.OrbicurveFiniteEtaleCoverMap (S2540ObjectMap B) (S2540ObjectMap A)) :
    (S2544AffineSchemeMap h0).left ≫ (invCover A).obj.hom = (invCover B).obj.hom := by
  have h2 : S1742HomOfStrongTrans
      (Pseudofunctor.StrongTrans.vcomp h0.map ((S2517InvObj (invCover A)).map)) =
      S1742HomOfStrongTrans ((S2517InvObj (invCover B)).map) :=
    S1742HomOfStrongTrans_congr h0.commutes
  rw [S1742HomOfStrongTrans_vcomp] at h2
  simp only [S2517InvObj, S2517StackHomOrb,
    S1742HomOfStrongTrans_strongTransOfHom] at h2
  have hleft := congrArg CategoryTheory.Over.Hom.left h2
  simpa [S2544AffineSchemeMap, S2517OverMap] using hleft

/-- D3: the affine cover hom underlying a cover map between the S2538-inverse
objects. -/
noncomputable def coverHomOf
    (h0 : Iut.OrbicurveFiniteEtaleCoverMap (S2540ObjectMap B) (S2540ObjectMap A)) :
    invCover B ⟶ invCover A :=
  ObjectProperty.homMk
    (CategoryTheory.Over.homMk (S2544AffineSchemeMap h0).left (coverHomOf_w h0))

/-- D3: the algebra hom A → B obtained from a cover hom by the S2538 equivalence. -/
noncomputable def algHomOf
    (h0 : Iut.OrbicurveFiniteEtaleCoverMap (S2540ObjectMap B) (S2540ObjectMap A)) :
    A ⟶ B :=
  Quiver.Hom.unop
    ((S2538AffineCoverEquiv.counitIso.app (Opposite.op B)).inv ≫
      S2538AffineCoverEquiv.functor.map (coverHomOf h0) ≫
      (S2538AffineCoverEquiv.counitIso.app (Opposite.op A)).hom)

/-- The algebra hom is the S2541 cover-hom-to-algebra map, transported along the
unit and counit isomorphisms of the S2538 equivalence. -/
theorem algHomOf_eq_coverHomToAlg
    (h0 : Iut.OrbicurveFiniteEtaleCoverMap (S2540ObjectMap B) (S2540ObjectMap A)) :
    algHomOf h0 =
      (S2538AffineCoverEquiv.counitIso.app (Opposite.op A)).hom.unop ≫
        S2541CoverHomToAlg (coverHomOf h0) ≫
        (S2538AffineCoverEquiv.counitIso.app (Opposite.op B)).inv.unop := by
  unfold algHomOf S2541CoverHomToAlg
  rw [unop_comp, unop_comp, Category.assoc]

/-- The algebra hom of D3 indeed induces the cover hom of D3 through the S2538
equivalence. -/
theorem inverse_map_algHomOf
    (h0 : Iut.OrbicurveFiniteEtaleCoverMap (S2540ObjectMap B) (S2540ObjectMap A)) :
    S2538AffineCoverEquiv.inverse.map (Quiver.Hom.op (algHomOf h0)) =
      coverHomOf h0 := by
  have hnat : S2538AffineCoverEquiv.unit.app (invCover B) ≫
      S2538AffineCoverEquiv.inverse.map
        (S2538AffineCoverEquiv.functor.map (coverHomOf h0)) =
    coverHomOf h0 ≫ S2538AffineCoverEquiv.unit.app (invCover A) :=
    S2538AffineCoverEquiv.unit_naturality (coverHomOf h0)
  have hB : S2538AffineCoverEquiv.inverse.map
        (S2538AffineCoverEquiv.counitIso.app (Opposite.op B)).inv =
      S2538AffineCoverEquiv.unit.app (invCover B) :=
    (S2538AffineCoverEquiv.unit_app_inverse (Opposite.op B)).symm
  have hA : S2538AffineCoverEquiv.inverse.map
        (S2538AffineCoverEquiv.counitIso.app (Opposite.op A)).hom =
      S2538AffineCoverEquiv.unitInv.app (invCover A) :=
    (S2538AffineCoverEquiv.unitInv_app_inverse (Opposite.op A)).symm
  have hop : Quiver.Hom.op (algHomOf h0) =
      (S2538AffineCoverEquiv.counitIso.app (Opposite.op B)).inv ≫
        S2538AffineCoverEquiv.functor.map (coverHomOf h0) ≫
        (S2538AffineCoverEquiv.counitIso.app (Opposite.op A)).hom :=
    Quiver.Hom.op_unop _
  rw [hop, Functor.map_comp, Functor.map_comp, hB, hA]
  rw [← Category.assoc, hnat]
  rw [Category.assoc, S2538AffineCoverEquiv.unitIso_hom_inv_id_app, Category.comp_id]

/-- D3: the corrected algebra cover map of the constructed algebra hom is the
constructed cover hom. -/
theorem S2543AlgCoverMapR_algHomOf
    (h0 : Iut.OrbicurveFiniteEtaleCoverMap (S2540ObjectMap B) (S2540ObjectMap A)) :
    S2543AlgCoverMapR (A := A) (B := B) (algHomOf h0) = coverHomOf h0 := by
  unfold S2543AlgCoverMapR
  exact inverse_map_algHomOf h0

/-- D4: the S2518 cover map of the constructed cover hom is 2-isomorphic to the
original cover map. -/
theorem coverMapRel_coverHomOf
    (h0 : Iut.OrbicurveFiniteEtaleCoverMap (S2540ObjectMap B) (S2540ObjectMap A)) :
    S1728CoverMapRel (S2518InvCoverMap (coverHomOf h0)) h0 := by
  have hscheme : S2518InvSchemeMap (coverHomOf h0) = S2544AffineSchemeMap h0 := by
    apply CategoryTheory.Over.OverMorphism.ext
    rfl
  refine ⟨(eqToIso (congrArg S1742StrongTransOfHom hscheme)).trans ?_⟩
  simpa only [S2544AffineSchemeMap] using S1742StrongTransIsoOfHom h0.map

/-- D5: the corrected quotient map is surjective. -/
theorem S2543QuotMapRSurjective_holds : S2543QuotMapRSurjective := by
  intro A B q
  induction q using Quot.inductionOn with
  | h h0 =>
    refine ⟨algHomOf h0, ?_⟩
    unfold S2543QuotMapR
    rw [S2543AlgCoverMapR_algHomOf h0]
    exact Quot.sound (coverMapRel_coverHomOf h0)

#check S2543QuotMapRSurjective_holds
#print axioms S2543QuotMapRSurjective_holds
#print axioms algHomOf_eq_coverHomToAlg

end LeanFormal.IUT.XiFPaper.FullD3D4Agent
end
