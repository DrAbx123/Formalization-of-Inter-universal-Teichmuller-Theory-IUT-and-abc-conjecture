import tmp.sheaf.xif.paper.S1988HComparisonNaturalityActual

/-!
# S1998: the prestack half of the iso-comma stack -- `S1956IsoCommaPrestack` proved

## Context

S1988 closed the H-comparison naturality statement
`S1956HComparisonNaturalityAll`.  The exact next missing for the prestack half
of S1956/S1864 (b) was

  `S1956IsoCommaPrestack f g` = `(sitePseudofunctor f g).IsPrestack J`,

i.e. the sheaf condition for the hom presheaves of the iso-comma
site pseudofunctor of the two actual finite-etale cover maps `f : A ⟶ C` and
`g : B ⟶ C`.  This file proves it.

## What is proved

1.  **The structure morphism of a restricted iso-comma object**
    (`S1998ObjHom`): at `Y : (Over S)ᵒᵖ` the structure isomorphism of
    `Y^* M` is the f-side naturality comparison, the C-side restriction of the
    structure isomorphism of `M`, and the g-side naturality comparison.

2.  **The pointwise fibre-product identification** (`S1998CommaCondition_iff`):
    the comma condition for a pair `(u, v)` in the A- and B-fibres is
    equivalent to the equation between the two H-comparison components
    `FstToH(u) ≫ N.hom = M.hom ≫ SndToH(v)` in the common C-hom presheaf.
    The algebra is isolated in the generic lemma `S1998_conj_iff`.

3.  **Compatibility of `pullHom` with postcomposition and precomposition**
    (`S1998pullHom_post`, `S1998pullHom_pre` and their raw forms): the
    restrictions of a hom presheaf commute with postcomposition with a fixed
    morphism of the target and precomposition with a fixed morphism of the
    source.

4.  **The two H-comparisons into the common C-hom presheaf**
    (`S1998FstToCommon`, `S1998SndToCommon`): the component maps of S1956,
    postcomposed or precomposed with the C-side structure isomorphism, are natural
    transformations into `C.presheafHom (f M.left) (g N.right)`.

5.  **The fibre-product closure** (`S1998IsSheaf_fibreProduct`): the pointwise
    fibre product of two natural transformations between sheaves of types is a
    sheaf.  The proof is the direct compatible-family argument: the two
    components glue because the corner presheaves are sheaves, and the equation
    holds by separatedness of the third one.

6.  **The identification of the hom presheaf with the fibre product**
    (`S1998HomFibreProductIso`): `P.presheafHom M N` is naturally isomorphic
    to the pointwise fibre product of `S1998FstToCommon` and
    `S1998SndToCommon`.  The componentwise bijection is the projection to the
    two fibres together with `S1998CommaCondition_iff`; naturality is the
    naturality of the two leg projections.

7.  **The prestack half** (`S1998IsoCommaPrestack`):
    `S1956IsoCommaPrestack f g`.  The three corner hom presheaves are sheaves
    because the three stacks `A.source`, `B.source`, `C.source` are
    prestacks; the fibre product is a sheaf by (5), and the hom presheaf is a
    sheaf by (6).

## Honest boundary

The effectivity half `S1956IsoCommaEffectivity f g` is **not** addressed here;
the stack statement `S1956IsoCommaStack` remains the conjunction of this file's
result and effectivity.  No `sorry`, no `axiom`, no `Shrink`, `ULift` or
`PUnit`, and no change of the target.  The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`; see the `#print axioms` block.
-/


noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1998IsoCommaPrestackActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1891PullbackStackIsStackActual
open LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S1970IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual
open LeanFormal.IUT.XiFPaper.S1988HComparisonNaturalityActual

universe u

abbrev K := S1726K
abbrev Site := SchemeOverField K
abbrev J : GrothendieckTopology Site := SchemeOverField.etaleTopology K

abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

abbrev IsoCommaObjAt {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (S : Site) :=
  S1836IsoComma (f.map.app (U S)).toFunctor (g.map.app (U S)).toFunctor

/-! ## 1. The structure morphism of a restricted iso-comma object -/

section ObjHom

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {S : Site} (M : IsoCommaObjAt f g S)

/-- **The structure morphism of the restricted iso-comma object.**  At
`Y : (Over S)ᵒᵖ` the structure isomorphism of `Y^* M` is the f-side naturality
comparison, the C-side restriction of the structure isomorphism of `M`, and the
g-side naturality comparison. -/
theorem S1998ObjHom (Y : (Over S)ᵒᵖ) :
    (((sitePseudofunctor f g).map (Y.unop.hom.op.toLoc)).toFunctor.obj M).obj.hom =
      (S1864SiteComparisonLeft f (Y.unop.hom.op.toLoc)).hom.app M.obj.left
        ≫ ((C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor.map M.obj.hom)
        ≫ (S1864SiteComparisonRight g (Y.unop.hom.op.toLoc)).hom.app M.obj.right := by
  change ((S1864IsoCommaRestrict (A.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor
      (B.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor
      (C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor
      (S1864SiteComparisonLeft f (Y.unop.hom.op.toLoc))
      (S1864SiteComparisonRight g (Y.unop.hom.op.toLoc))).obj M).obj.hom = _
  rw [S1864IsoCommaRestrict_obj_hom]
  rfl

end ObjHom

/-! ## 2. The generic cancellation lemma -/

/-- **The generic cancellation lemma** underlying the fibre-product identification:
conjugation by four isomorphisms identifies the two displayed equations. -/
theorem S1998_conj_iff {D : Type*} [Category D]
    {A0 A0' B0 B0' X0 X0' Y0 Y0' : D}
    (l : A0' ≅ A0) (l' : X0' ≅ X0) (r : B0 ≅ B0') (r' : Y0 ≅ Y0')
    (p : A0' ⟶ X0') (q : X0 ⟶ Y0) (s : A0 ⟶ B0) (t : B0' ⟶ Y0') :
    (p ≫ l'.hom ≫ q ≫ r'.hom = l.hom ≫ s ≫ r.hom ≫ t) ↔
      (l.inv ≫ p ≫ l'.hom ≫ q = s ≫ r.hom ≫ t ≫ r'.inv) := by
  constructor
  · intro h
    apply (cancel_mono r'.hom).mp
    calc
      (l.inv ≫ p ≫ l'.hom ≫ q) ≫ r'.hom
          = l.inv ≫ (p ≫ l'.hom ≫ q ≫ r'.hom) := by simp only [Category.assoc]
      _ = l.inv ≫ (l.hom ≫ s ≫ r.hom ≫ t) := by rw [h]
      _ = s ≫ r.hom ≫ t := by rw [Iso.inv_hom_id_assoc]
      _ = (s ≫ r.hom ≫ t) ≫ (r'.inv ≫ r'.hom) := by
            rw [Iso.inv_hom_id, Category.comp_id]
      _ = (s ≫ r.hom ≫ t ≫ r'.inv) ≫ r'.hom := by simp only [Category.assoc]
  · intro h
    have h' : l.hom ≫ (l.inv ≫ p ≫ l'.hom ≫ q) ≫ r'.hom
        = l.hom ≫ (s ≫ r.hom ≫ t ≫ r'.inv) ≫ r'.hom := by rw [h]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h'

/-! ## 3. The comma condition and the H-comparison equation -/

section CommaCondition

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {S : Site} (M N : IsoCommaObjAt f g S)

/-- **The common C-hom presheaf** into which both H-comparisons map. -/
abbrev S1998CommonHom : (Over S)ᵒᵖ ⥤ Type :=
  Pseudofunctor.presheafHom C.source.fiber (S := S)
    ((f.map.app (U S)).toFunctor.obj M.obj.left)
    ((g.map.app (U S)).toFunctor.obj N.obj.right)

/-- **The comma condition** for a pair of morphisms of the A- and B-fibres at
`Y : (Over S)ᵒᵖ`: the two legs satisfy the structure equation of the iso-comma. -/
def S1998CommaCondition (Y : (Over S)ᵒᵖ)
    (u : (Pseudofunctor.presheafHom A.source.fiber (S := S) M.obj.left N.obj.left).obj Y)
    (v : (Pseudofunctor.presheafHom B.source.fiber (S := S) M.obj.right N.obj.right).obj Y) : Prop :=
  (f.map.app (U Y.unop.left)).toFunctor.map u
      ≫ (((sitePseudofunctor f g).map (Y.unop.hom.op.toLoc)).toFunctor.obj N).obj.hom =
    (((sitePseudofunctor f g).map (Y.unop.hom.op.toLoc)).toFunctor.obj M).obj.hom
      ≫ (g.map.app (U Y.unop.left)).toFunctor.map v

/-- **The pointwise fibre-product identification.**  The comma condition is
equivalent to the equality of the two H-comparison components into the common
C-hom presheaf. -/
theorem S1998CommaCondition_iff (Y : (Over S)ᵒᵖ)
    (u : (Pseudofunctor.presheafHom A.source.fiber (S := S) M.obj.left N.obj.left).obj Y)
    (v : (Pseudofunctor.presheafHom B.source.fiber (S := S) M.obj.right N.obj.right).obj Y) :
    S1998CommaCondition f g M N Y u v ↔
      S1956FstToHComponent f g M N Y u
          ≫ ((C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor.map N.obj.hom) =
        ((C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor.map M.obj.hom)
          ≫ S1956SndToHComponent f g M N Y v := by
  unfold S1998CommaCondition S1956FstToHComponent S1956SndToHComponent
  rw [S1998ObjHom f g M Y, S1998ObjHom f g N Y]
  simp only [Category.assoc]
  exact S1998_conj_iff
    (l := (S1864SiteComparisonLeft f (Y.unop.hom.op.toLoc)).app M.obj.left)
    (l' := (S1864SiteComparisonLeft f (Y.unop.hom.op.toLoc)).app N.obj.left)
    (r := (S1864SiteComparisonRight g (Y.unop.hom.op.toLoc)).app M.obj.right)
    (r' := (S1864SiteComparisonRight g (Y.unop.hom.op.toLoc)).app N.obj.right)
    (p := (f.map.app (U Y.unop.left)).toFunctor.map u)
    (q := (C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor.map N.obj.hom)
    (s := (C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor.map M.obj.hom)
    (t := (g.map.app (U Y.unop.left)).toFunctor.map v)

end CommaCondition

/-! ## 4. Compatibility of `pullHom` with postcomposition and precomposition -/

section PullHomComp

variable {F : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
  {S : Site} {a b c : F.obj (U S)}

/-- **Raw pullback of a postcomposed morphism.** -/
theorem S1998pullHom_post_raw (w : b ⟶ c) {Y Z : (Over S)ᵒᵖ} (p : Y ⟶ Z)
    (u : (F.map (Y.unop.hom.op.toLoc)).toFunctor.obj a ⟶
      (F.map (Y.unop.hom.op.toLoc)).toFunctor.obj b) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
        (u ≫ (F.map (Y.unop.hom.op.toLoc)).toFunctor.map w) p.unop.left
        Z.unop.hom Z.unop.hom =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) u p.unop.left
          Z.unop.hom Z.unop.hom
        ≫ (F.map (Z.unop.hom.op.toLoc)).toFunctor.map w := by
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  simp only [Functor.map_comp, Category.assoc]
  simp

/-- **Raw pullback of a precomposed morphism.** -/
theorem S1998pullHom_pre_raw (w : a ⟶ b) {Y Z : (Over S)ᵒᵖ} (p : Y ⟶ Z)
    (v : (F.map (Y.unop.hom.op.toLoc)).toFunctor.obj b ⟶
      (F.map (Y.unop.hom.op.toLoc)).toFunctor.obj c) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
        ((F.map (Y.unop.hom.op.toLoc)).toFunctor.map w ≫ v) p.unop.left
        Z.unop.hom Z.unop.hom =
      (F.map (Z.unop.hom.op.toLoc)).toFunctor.map w
        ≫ Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) v p.unop.left
          Z.unop.hom Z.unop.hom := by
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  simp only [Functor.map_comp, Category.assoc]
  simp

/-- **Pullback of a postcomposed morphism** (presheaf form). -/
theorem S1998pullHom_post (w : b ⟶ c) {Y Z : (Over S)ᵒᵖ} (p : Y ⟶ Z)
    (u : (Pseudofunctor.presheafHom F (S := S) a b).obj Y) :
    (Pseudofunctor.presheafHom F (S := S) a c).map p
        (u ≫ (F.map (Y.unop.hom.op.toLoc)).toFunctor.map w) =
      (Pseudofunctor.presheafHom F (S := S) a b).map p u
        ≫ (F.map (Z.unop.hom.op.toLoc)).toFunctor.map w := by
  simpa only [Pseudofunctor.presheafHom, ConcreteCategory.hom_ofHom, TypeCat.Fun.toFun_apply,
    TypeCat.Fun.coe_mk] using
    S1998pullHom_post_raw (F := F) (a := a) (b := b) (c := c) w p u

/-- **Pullback of a precomposed morphism** (presheaf form). -/
theorem S1998pullHom_pre (w : a ⟶ b) {Y Z : (Over S)ᵒᵖ} (p : Y ⟶ Z)
    (v : (Pseudofunctor.presheafHom F (S := S) b c).obj Y) :
    (Pseudofunctor.presheafHom F (S := S) a c).map p
        ((F.map (Y.unop.hom.op.toLoc)).toFunctor.map w ≫ v) =
      (F.map (Z.unop.hom.op.toLoc)).toFunctor.map w
        ≫ (Pseudofunctor.presheafHom F (S := S) b c).map p v := by
  simpa only [Pseudofunctor.presheafHom, ConcreteCategory.hom_ofHom, TypeCat.Fun.toFun_apply,
    TypeCat.Fun.coe_mk] using
    S1998pullHom_pre_raw (F := F) (a := a) (b := b) (c := c) w p v

end PullHomComp

/-! ## 5. The two H-comparisons into the common C-hom presheaf -/

section NatTrans

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {S : Site} (M N : IsoCommaObjAt f g S)

/-- **The first H-comparison into the common C-hom presheaf**: postcompose the
component with the C-side structure isomorphism of the target. -/
noncomputable def S1998FstToCommon :
    Pseudofunctor.presheafHom A.source.fiber (S := S) M.obj.left N.obj.left ⟶
      S1998CommonHom f g M N where
  app Y := ↾fun u =>
    S1956FstToHComponent f g M N Y u
      ≫ ((C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor.map N.obj.hom)
  naturality {Y Z} p := by
    ext u
    change S1956FstToHComponent f g M N Z
        ((Pseudofunctor.presheafHom A.source.fiber (S := S) M.obj.left N.obj.left).map p u)
        ≫ ((C.source.fiber.map (Z.unop.hom.op.toLoc)).toFunctor.map N.obj.hom) =
      (S1998CommonHom f g M N).map p
        (S1956FstToHComponent f g M N Y u
          ≫ ((C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor.map N.obj.hom))
    rw [S1956FstToHComponent_eq f g M N Z, S1956FstToHComponent_eq f g M N Y]
    rw [S1988HComponent_naturality f.map M.obj.left N.obj.left Y Z p u]
    exact (S1998pullHom_post_raw (F := C.source.fiber) N.obj.hom p
      (S1988HComponent f.map M.obj.left N.obj.left Y u)).symm

/-- **The second H-comparison into the common C-hom presheaf**: precompose the
component with the C-side structure isomorphism of the source. -/
noncomputable def S1998SndToCommon :
    Pseudofunctor.presheafHom B.source.fiber (S := S) M.obj.right N.obj.right ⟶
      S1998CommonHom f g M N where
  app Y := ↾fun v =>
    ((C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor.map M.obj.hom)
      ≫ S1956SndToHComponent f g M N Y v
  naturality {Y Z} p := by
    ext v
    change ((C.source.fiber.map (Z.unop.hom.op.toLoc)).toFunctor.map M.obj.hom)
        ≫ S1956SndToHComponent f g M N Z
          ((Pseudofunctor.presheafHom B.source.fiber (S := S) M.obj.right N.obj.right).map p v) =
      (S1998CommonHom f g M N).map p
        (((C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor.map M.obj.hom)
          ≫ S1956SndToHComponent f g M N Y v)
    rw [S1956SndToHComponent_eq f g M N Z, S1956SndToHComponent_eq f g M N Y]
    rw [S1988HComponent_naturality g.map M.obj.right N.obj.right Y Z p v]
    exact (S1998pullHom_pre_raw (F := C.source.fiber) M.obj.hom p
      (S1988HComponent g.map M.obj.right N.obj.right Y v)).symm

end NatTrans

/-! ## 6. The pointwise fibre product of two natural transformations -/

section FibreProduct

universe w

variable {D : Type w} [Category D] {K : GrothendieckTopology D}
  {P Q R : Dᵒᵖ ⥤ Type} (FA : P ⟶ R) (FB : Q ⟶ R)

/-- **The object of the pointwise fibre product** of two natural
transformations of `Type`-valued presheaves. -/
def S1998FibreProductObj (Y : Dᵒᵖ) : Type :=
  { x : P.obj Y × Q.obj Y // FA.app Y x.1 = FB.app Y x.2 }

/-- **The pointwise fibre product of two natural transformations of
`Type`-valued presheaves.** -/
def S1998FibreProduct : Dᵒᵖ ⥤ Type where
  obj := S1998FibreProductObj FA FB
  map {Y Z} p := ↾fun x =>
    ⟨(P.map p x.1.1, Q.map p x.1.2), by
      change FA.app Z (P.map p x.1.1) = FB.app Z (Q.map p x.1.2)
      rw [NatTrans.naturality_apply FA p, NatTrans.naturality_apply FB p, x.2]⟩
  map_id Y := by
    ext x
    apply Subtype.ext
    apply Prod.ext <;> simp
  map_comp f g := by
    ext x
    apply Subtype.ext
    apply Prod.ext <;> simp

/-- The underlying pair of a restriction in the fibre product. -/
theorem S1998FibreProduct_map_val {Y Z : Dᵒᵖ} (p : Y ⟶ Z)
    (x : S1998FibreProductObj FA FB Y) :
    ((S1998FibreProduct FA FB).map p x).1 = (P.map p x.1.1, Q.map p x.1.2) := rfl

/-- The first component of a restriction in the fibre product. -/
theorem S1998FibreProduct_map_fst {Y Z : Dᵒᵖ} (p : Y ⟶ Z)
    (x : S1998FibreProductObj FA FB Y) :
    ((S1998FibreProduct FA FB).map p x).1.1 = P.map p x.1.1 := rfl

/-- The second component of a restriction in the fibre product. -/
theorem S1998FibreProduct_map_snd {Y Z : Dᵒᵖ} (p : Y ⟶ Z)
    (x : S1998FibreProductObj FA FB Y) :
    ((S1998FibreProduct FA FB).map p x).1.2 = Q.map p x.1.2 := rfl

/-- The first projection of the fibre product. -/
def S1998FibreProductFst : S1998FibreProduct FA FB ⟶ P where
  app Y := ↾fun x => x.1.1
  naturality {Y Z} p := by
    ext x
    show ((S1998FibreProduct FA FB).map p x).1.1 = P.map p x.1.1
    exact S1998FibreProduct_map_fst FA FB p x

/-- The second projection of the fibre product. -/
def S1998FibreProductSnd : S1998FibreProduct FA FB ⟶ Q where
  app Y := ↾fun x => x.1.2
  naturality {Y Z} p := by
    ext x
    show ((S1998FibreProduct FA FB).map p x).1.2 = Q.map p x.1.2
    exact S1998FibreProduct_map_snd FA FB p x

/-- **A pointwise fibre product of sheaves of types is a sheaf.** -/
theorem S1998IsSheaf_fibreProduct
    (hP : Presieve.IsSheaf K P) (hQ : Presieve.IsSheaf K Q) (hR : Presieve.IsSheaf K R) :
    Presieve.IsSheaf K (S1998FibreProduct FA FB) := by
  intro X S hS x hx
  let xP : Presieve.FamilyOfElements P (S : Presieve X) := fun Y f hf => (x f hf).1.1
  let xQ : Presieve.FamilyOfElements Q (S : Presieve X) := fun Y f hf => (x f hf).1.2
  have hxP : xP.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    simpa [S1998FibreProduct, xP] using congrArg (fun t => t.1.1) (hx g₁ g₂ h₁ h₂ w)
  have hxQ : xQ.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    simpa [S1998FibreProduct, xQ] using congrArg (fun t => t.1.2) (hx g₁ g₂ h₁ h₂ w)
  let u := (hP S hS).amalgamate xP hxP
  let v := (hQ S hS).amalgamate xQ hxQ
  have huv : FA.app (Opposite.op X) u = FB.app (Opposite.op X) v := by
    apply (hR S hS).isSeparatedFor.ext
    intro Y f hf
    rw [← NatTrans.naturality_apply FA f.op, ← NatTrans.naturality_apply FB f.op]
    rw [show P.map f.op u = xP f hf from Presieve.IsSheafFor.valid_glue (hP S hS) hxP f hf]
    rw [show Q.map f.op v = xQ f hf from Presieve.IsSheafFor.valid_glue (hQ S hS) hxQ f hf]
    exact (x f hf).2
  refine ⟨⟨(u, v), huv⟩, ?_, ?_⟩
  · intro Y f hf
    apply Subtype.ext
    apply Prod.ext
    · simpa [S1998FibreProduct, xP] using Presieve.IsSheafFor.valid_glue (hP S hS) hxP f hf
    · simpa [S1998FibreProduct, xQ] using Presieve.IsSheafFor.valid_glue (hQ S hS) hxQ f hf
  · intro t ht
    apply Subtype.ext
    apply Prod.ext
    · exact ((hP S hS) xP hxP).unique
        (fun Y f hf => by simpa [S1998FibreProduct, xP] using congrArg (fun z => z.1.1) (ht f hf))
        (Presieve.IsSheafFor.isAmalgamation (hP S hS) hxP)
    · exact ((hQ S hS) xQ hxQ).unique
        (fun Y f hf => by simpa [S1998FibreProduct, xQ] using congrArg (fun z => z.1.2) (ht f hf))
        (Presieve.IsSheafFor.isAmalgamation (hQ S hS) hxQ)

end FibreProduct

/-! ## 7. The iso-comma hom presheaf is the fibre product -/

section Identification

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {S : Site} (M N : IsoCommaObjAt f g S)

/-- The hom presheaf of the iso-comma pseudofunctor. -/
abbrev S1998HomPresheaf {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {S : Site} (M N : IsoCommaObjAt f g S) : (Over S)ᵒᵖ ⥤ Type :=
  Pseudofunctor.presheafHom (sitePseudofunctor f g) M N

/-- The pointwise fibre product of the two H-comparison natural transformations. -/
abbrev S1998HomFibreProduct {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {S : Site} (M N : IsoCommaObjAt f g S) : (Over S)ᵒᵖ ⥤ Type :=
  S1998FibreProduct (S1998FstToCommon f g M N) (S1998SndToCommon f g M N)

/-- **The componentwise bijection** between the hom presheaf of the iso-comma
and the fibre product of the A-, B- and C-hom presheaves. -/
noncomputable def S1998HomFibreProductEquiv {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) {S : Site} (M N : IsoCommaObjAt f g S) (Y : (Over S)ᵒᵖ) :
    (S1998HomPresheaf f g M N).obj Y ≃ (S1998HomFibreProduct f g M N).obj Y where
  toFun φ :=
    ⟨((S1956FstHomPresheaf f g M N).app Y φ, (S1956SndHomPresheaf f g M N).app Y φ), by
      show S1956FstToHComponent f g M N Y ((S1956FstHomPresheaf f g M N).app Y φ)
          ≫ ((C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor.map N.obj.hom) =
        ((C.source.fiber.map (Y.unop.hom.op.toLoc)).toFunctor.map M.obj.hom)
          ≫ S1956SndToHComponent f g M N Y ((S1956SndHomPresheaf f g M N).app Y φ)
      exact (S1998CommaCondition_iff f g M N Y _ _).1 φ.hom.w⟩
  invFun x :=
    ObjectProperty.homMk (CommaMorphism.mk x.1.1 x.1.2 (by
      show (f.map.app (U Y.unop.left)).toFunctor.map x.1.1
          ≫ (((sitePseudofunctor f g).map (Y.unop.hom.op.toLoc)).toFunctor.obj N).obj.hom =
        (((sitePseudofunctor f g).map (Y.unop.hom.op.toLoc)).toFunctor.obj M).obj.hom
          ≫ (g.map.app (U Y.unop.left)).toFunctor.map x.1.2
      exact (S1998CommaCondition_iff f g M N Y x.1.1 x.1.2).2 x.2))
  left_inv φ := by
    apply S1836IsoComma_hom_ext (f.map.app (U Y.unop.left)).toFunctor
      (g.map.app (U Y.unop.left)).toFunctor
    · rfl
    · rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> rfl

/-- **The identification of the iso-comma hom presheaf with the fibre product.** -/
noncomputable def S1998HomFibreProductIso :
    S1998HomPresheaf f g M N ≅ S1998HomFibreProduct f g M N :=
  NatIso.ofComponents (fun Y => (S1998HomFibreProductEquiv f g M N Y).toIso) (by
    intro Y Z p
    ext φ
    apply Subtype.ext
    apply Prod.ext
    · exact NatTrans.naturality_apply (S1956FstHomPresheaf f g M N) p φ
    · exact NatTrans.naturality_apply (S1956SndHomPresheaf f g M N) p φ)

end Identification

/-! ## 8. The prestack half -/

section Prestack

/-- **The prestack half for the actual iso-comma pseudofunctor**: the hom
presheaves of the iso-comma site pseudofunctor are sheaves for the over-site of
every test object. -/
theorem S1998IsoCommaPrestack {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S1956IsoCommaPrestack f g := by
  constructor
  intro S M N
  rw [isSheaf_iff_isSheaf_of_type]
  haveI hA : A.source.fiber.IsPrestack J := A.source.isStack.toIsPrestack
  haveI hB : B.source.fiber.IsPrestack J := B.source.isStack.toIsPrestack
  haveI hC : C.source.fiber.IsPrestack J := C.source.isStack.toIsPrestack
  have hP : Presieve.IsSheaf (J.over S)
      (Pseudofunctor.presheafHom A.source.fiber (S := S) M.obj.left N.obj.left) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Pseudofunctor.IsPrestack.isSheaf (F := A.source.fiber) J M.obj.left N.obj.left)
  have hQ : Presieve.IsSheaf (J.over S)
      (Pseudofunctor.presheafHom B.source.fiber (S := S) M.obj.right N.obj.right) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Pseudofunctor.IsPrestack.isSheaf (F := B.source.fiber) J M.obj.right N.obj.right)
  have hR : Presieve.IsSheaf (J.over S) (S1998CommonHom f g M N) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Pseudofunctor.IsPrestack.isSheaf (F := C.source.fiber) J
        ((f.map.app (U S)).toFunctor.obj M.obj.left)
        ((g.map.app (U S)).toFunctor.obj N.obj.right))
  exact Presieve.isSheaf_iso (J := J.over S) (P := S1998HomFibreProduct f g M N)
    (S1998HomFibreProductIso f g M N).symm
    (S1998IsSheaf_fibreProduct (S1998FstToCommon f g M N) (S1998SndToCommon f g M N)
      hP hQ hR)

/-- **The consumer.**  Together with the (still open) effectivity half, the
prestack half supplies the full stack condition of S1956/S1864 (b). -/
theorem S1998IsoCommaStack_of_effectivity {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (h : S1956IsoCommaEffectivity f g) : S1956IsoCommaStack f g :=
  (S1956IsoCommaStack_iff_prestack_effectivity f g).2
    ⟨S1998IsoCommaPrestack f g, h⟩

end Prestack

/-! ## 9. Checks and axiom audit -/

#check S1998ObjHom
#check S1998_conj_iff
#check S1998CommaCondition
#check S1998CommaCondition_iff
#check S1998pullHom_post_raw
#check S1998pullHom_pre_raw
#check S1998pullHom_post
#check S1998pullHom_pre
#check S1998FstToCommon
#check S1998SndToCommon
#check S1998FibreProductObj
#check S1998FibreProduct
#check S1998FibreProductFst
#check S1998FibreProductSnd
#check S1998IsSheaf_fibreProduct
#check S1998HomPresheaf
#check S1998HomFibreProduct
#check S1998HomFibreProductEquiv
#check S1998HomFibreProductIso
#check S1998IsoCommaPrestack
#check S1998IsoCommaStack_of_effectivity

#print axioms S1998ObjHom
#print axioms S1998_conj_iff
#print axioms S1998CommaCondition_iff
#print axioms S1998pullHom_post_raw
#print axioms S1998pullHom_pre_raw
#print axioms S1998pullHom_post
#print axioms S1998pullHom_pre
#print axioms S1998FstToCommon
#print axioms S1998SndToCommon
#print axioms S1998FibreProduct
#print axioms S1998IsSheaf_fibreProduct
#print axioms S1998HomFibreProductEquiv
#print axioms S1998HomFibreProductIso
#print axioms S1998IsoCommaPrestack
#print axioms S1998IsoCommaStack_of_effectivity

end LeanFormal.IUT.XiFPaper.S1998IsoCommaPrestackActual