import tmp.sheaf.xif.paper.S1738FiniteTypeSmallnessActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Skeletal

/-!
# S1761: finite-type DM-stack smallness and the actual orbicurve cover category

## Question

S1738 isolated the cardinality input needed by the actual orbicurve cover
category: Mathlib proves that affine schemes locally of finite type over a
fixed base scheme are essentially small, but the cover sources are
category-valued etale stacks, not schemes.  This file attacks the next step:

* can Mathlib's finite-type bound be upgraded to finite-type DM etale stacks
  over a field, or at least to the actual finite-etale cover category of an
  orbicurve?
* if not, what exactly is missing, stated with the actual Lean objects rather
  than with an abstract placeholder?

## What Mathlib actually has

* `AlgebraicGeometry.essentiallySmall_costructuredArrow_Spec`: the category
  of affine schemes locally of finite type over a fixed scheme is essentially
  small (reused from S1738).
* `MorphismProperty.CostructuredArrow` and the affine finite-etale slice are
  essentially small by the same theorem.  This is the small model used below.
* `Pseudofunctor.IsStack` and the descent machinery for category-valued
  pseudofunctors on a site.
* `CategoryTheory.EssentiallySmall`, `Skeleton`, `fromSkeleton` and the
  standard transfer lemmas.

Mathlib does **not** have algebraic stacks, Deligne-Mumford stacks, their
diagonals, etale atlases, stack quotients, or a theorem that a finite-type DM
stack is a quotient of a groupoid in finite-type schemes.  In particular there
is no Mathlib declaration of the form "finite-type DM stacks are essentially
small".

## What is proved unconditionally here

1. The affine finite-etale slice over an arbitrary scheme `S` is essentially
   small, hence so is its skeleton (Section 1).
2. Strict 2-Yoneda for representable etale stacks: every strong
   transformation between two representable stacks is *strictly* determined by
   its value at the identity (Section 2).  This closes S1738's
   `S1738TwoYonedaStrong` and gives `Small.{u}` for the raw strong
   transformation type, not merely for its 2-isomorphism classes.
3. Every representable etale stack is an actual etale stack, for every scheme
   over the field, not only for the S1726 model (Section 2).
4. For arbitrary schemes `U R` and maps `s t : R ⟶ U`, the category of
   **raw finite-etale descent data** along `s,t` is essentially small
   (Section 3).  Its objects are an affine finite-etale scheme over `U`
   together with an isomorphism between its two pullbacks to `R`; no
   cocycle condition is imposed, so the actual descent category (a full
   subcategory) is also essentially small.
5. If the actual cover category is equivalent to a full subcategory of that
   raw descent category, then it is essentially small.  This is the precise
   descent-transfer theorem (Section 4).

## What remains missing (precise)

The missing geometric input is split into two named statements:

* `S1761FiniteTypeDMAtlasExistence X`: a finite-type separated DM stack over
  the field admits an affine finite-type etale atlas whose self-fiber-product
  is again affine of finite type.  This is the Mathlib-missing
  algebraic/DM-stack atlas theorem.  For the S1726 orbicurve the stack is
  representable by the affine Weierstrass model, so the intended atlas is the
  identity; the file does not assert the general theorem.
* `S1761FiniteTypeDMCoverDescent X`: for such an atlas, the actual finite-
  etale cover category of `X` is equivalent to the full subcategory of raw
  descent data satisfying the cocycle condition.  This is the stack descent
  theorem along an atlas; Mathlib's `IsStack` is descent for a cover in the
  site of schemes, not for a morphism of stacks `U ⟶ X`.

The file proves that these two statements imply
`EssentiallySmall.{u} (OrbicurveFiniteEtaleCover X)` for an orbicurve whose
stack has such an atlas.  It does **not** assert either missing statement.

## Honest boundary

No `sorry`, no `axiom`, no `Shrink`, no `ULift`, no `PLift`, no
`PUnit`, and no fake category.  `Skeleton` is Mathlib's genuine categorical
skeleton, used only to name the small model furnished by
`EssentiallySmall`; it is not a `Shrink`/`ULift` substitute for a
mathematical smallness proof.  The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1761DMStackSmallnessActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open Iut
open scoped SpecOfNotation
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1738FiniteTypeSmallnessActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

universe u

variable {F : Type u} [Field F]

/-! ## 1. The unconditional scheme-level bounds -/

/-- Mathlib's affine locally-finite-type bound, in the form used by the
orbifold base. -/
theorem S1761_affineFiniteType_essentiallySmall (Y : Scheme.{u}) :
    EssentiallySmall.{u}
      (S1738LocallyOfFiniteType.{u}.CostructuredArrow ⊤ Scheme.Spec Y) :=
  S1738_affineLocallyOfFiniteType_essentiallySmall Y

/-- The same bound over the field itself. -/
theorem S1761_affineField_essentiallySmall (F' : Type u) [Field F'] :
    EssentiallySmall.{u}
      (S1738LocallyOfFiniteType.{u}.CostructuredArrow ⊤ Scheme.Spec (Spec(F'))) :=
  S1738_affineField_essentiallySmall F'

/-- Finite etale morphisms, as a Mathlib morphism property. -/
abbrev S1761FiniteEtale : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale

instance : S1761FiniteEtale.{u}.RespectsIso :=
  inferInstanceAs ((@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).RespectsIso)

lemma S1761FiniteEtale_le_locallyOfFiniteType :
    S1761FiniteEtale.{u} ≤ @LocallyOfFiniteType := by
  intro X Y f hf
  haveI : IsFinite f := hf.1
  exact inferInstance

/-- **Unconditional**: the affine finite-etale slice over any scheme is
essentially small.  This is the small model that the descent construction
below uses. -/
theorem S1761AffineFiniteEtaleSlice_essentiallySmall (S : Scheme.{u}) :
    EssentiallySmall.{u} (S1761FiniteEtale.{u}.CostructuredArrow ⊤ Scheme.Spec S) :=
  essentiallySmall_costructuredArrow_Spec S1761FiniteEtale
    S1761FiniteEtale_le_locallyOfFiniteType

/-- The concrete field case: affine finite-etale schemes over `Spec F` are
essentially small.  This is the unconditional "finite-etale covers of a
point" bound. -/
theorem S1761FieldFiniteEtale_essentiallySmall :
    EssentiallySmall.{u}
      (S1761FiniteEtale.{u}.CostructuredArrow ⊤ Scheme.Spec (Spec(F))) :=
  S1761AffineFiniteEtaleSlice_essentiallySmall (Spec(F))

/-- The underlying type of the affine finite-etale slice. -/
abbrev S1761FiniteEtaleSlice (S : Scheme.{u}) : Type (u + 1) :=
  S1761FiniteEtale.{u}.CostructuredArrow ⊤ Scheme.Spec S

instance (S : Scheme.{u}) : EssentiallySmall.{u} (S1761FiniteEtaleSlice S) :=
  S1761AffineFiniteEtaleSlice_essentiallySmall S

/-! ## 2. Strict 2-Yoneda and smallness of representable stack homs -/

/-- An isomorphism type is a subsingleton whenever its hom type is. -/
instance S1761IsoSubsingletonOfHomSubsingleton {C : Type u} [Category.{u} C]
    {X Y : C} [Subsingleton (X ⟶ Y)] : Subsingleton (X ≅ Y) where
  allEq e1 e2 := by
    apply Iso.ext
    exact Subsingleton.elim _ _

/-- The 2-cells between two morphisms of representable stacks are
subsingletons.  This is the discreteness computation of S1738. -/
instance S1761CatHom₂Subsingleton (S T : SchemeOverField F)
    {a b : LocallyDiscrete (SchemeOverField F)ᵒᵖ}
    (phi psi : (S1738R S).obj a ⟶ (S1738R T).obj b) :
    Subsingleton (phi ⟶ psi) :=
  S1738R_hom₂_subsingleton S T phi psi

/-- Two strong transformations of representable stacks with the same
component functions are equal.  The remaining fields are either
proof-irrelevant or isomorphisms between functors into discrete categories,
hence subsingletons. -/
theorem S1761StrongTrans_ext (S T : SchemeOverField F)
    (eta theta : Pseudofunctor.StrongTrans (S1738R S) (S1738R T))
    (h : ∀ a, eta.app a = theta.app a) : eta = theta := by
  cases eta with
  | mk app nat natn natid natcomp =>
    cases theta with
    | mk app' nat' natn' natid' natcomp' =>
      simp only at h
      have h' : app = app' := funext h
      subst h'
      congr 1
      funext a b f
      exact Subsingleton.elim _ _

/-- **S1738's missing strict 2-Yoneda statement, now proved.** -/
theorem S1761TwoYonedaStrong (S T : SchemeOverField F) :
    S1738TwoYonedaStrong S T := by
  intro eta
  apply S1761StrongTrans_ext
  intro a
  apply Cat.ext
  apply Discrete.functor_ext
  intro g
  exact Discrete.ext (S1738_app_eq_of_eval S T eta g)

/-- The S1738 packaged form: 2-Yoneda holds for every pair of representing
schemes. -/
theorem S1761TwoYonedaRequired : S1738TwoYonedaRequired (F := F) :=
  fun S T => S1761TwoYonedaStrong S T

/-- **Unconditional**: the raw type of strong transformations between two
representable etale stacks is small at the base universe.  This is stronger
than smallness of the 2-isomorphism quotient. -/
theorem S1761StrongTrans_small (S T : SchemeOverField F) :
    Small.{u} (Pseudofunctor.StrongTrans (S1738R S) (S1738R T)) :=
  S1738StrongTrans_small_of_twoYoneda S T (S1761TwoYonedaStrong S T)

/-- Every representable etale stack over the field is an actual etale stack.
This uses the constructed discrete-sheaf-to-stack bridge of S1419, not a new
axiom. -/
theorem S1761RepresentableIsStack (U : SchemeOverField F) :
    (S1738R U).IsStack (SchemeOverField.etaleTopology F) := by
  have hP : Presieve.IsSheaf (SchemeOverField.etaleTopology F) (yoneda.obj U) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (representableEtalePresheaf_isSheaf (F := F) U)
  change (discretePseudo (C := SchemeOverField F) (yoneda.obj U)).IsStack
    (SchemeOverField.etaleTopology F)
  exact DiscreteSheafStack.discretePseudo_isStack (P := yoneda.obj U) hP

/-- The etale stack represented by a scheme over the field. -/
def S1761RepresentableStack (U : SchemeOverField F) : EtaleStackOverField F where
  fiber := S1738R U
  isStack := S1761RepresentableIsStack U

/-! ## 3. Raw finite-etale descent data are essentially small -/

/-- The small skeleton of the affine finite-etale slice over `U`. -/
abbrev S1761FiniteEtaleIndex (U : Scheme.{u}) := Skeleton (S1761FiniteEtaleSlice U)

instance (U : Scheme.{u}) : Small.{u} (S1761FiniteEtaleIndex U) :=
  small_skeleton_of_essentiallySmall (C := S1761FiniteEtaleSlice U)

/-- The affine finite-etale scheme selected by a skeleton index. -/
noncomputable def S1761FiniteEtaleObj (U : Scheme.{u}) (i : S1761FiniteEtaleIndex U) :
    S1761FiniteEtaleSlice U :=
  (fromSkeleton (S1761FiniteEtaleSlice U)).obj i

/-- The same object, regarded as a scheme over `U`. -/
noncomputable def S1761FiniteEtaleOver (U : Scheme.{u}) (i : S1761FiniteEtaleIndex U) :
    Over U :=
  (MorphismProperty.Over.forget S1761FiniteEtale ⊤ U).obj
    ((MorphismProperty.CostructuredArrow.toOver S1761FiniteEtale Scheme.Spec U).obj
      (S1761FiniteEtaleObj U i))

/-- Raw descent data along two maps `s t : R ⟶ U`: an affine finite-etale
scheme over `U` together with an isomorphism between its two pullbacks to
`R`.  The cocycle condition is not imposed here; the actual descent category
is a full subcategory, so smallness of this raw category implies smallness of
every cocycle subcategory. -/
structure S1761RawDescent {U R : Scheme.{u}} (s t : R ⟶ U) where
  V : S1761FiniteEtaleIndex U
  φ : (Over.pullback s).obj (S1761FiniteEtaleOver U V) ≅
    (Over.pullback t).obj (S1761FiniteEtaleOver U V)

/-- Morphisms of raw descent data: a morphism over `U` compatible with the
two descent isomorphisms. -/
structure S1761RawDescentHom {U R : Scheme.{u}} {s t : R ⟶ U}
    (X Y : S1761RawDescent s t) where
  f : S1761FiniteEtaleOver U X.V ⟶ S1761FiniteEtaleOver U Y.V
  commutes : (Over.pullback s).map f ≫ Y.φ.hom = X.φ.hom ≫ (Over.pullback t).map f

attribute [ext] S1761RawDescentHom

instance {U R : Scheme.{u}} {s t : R ⟶ U} (X Y : S1761RawDescent s t) :
    Small.{u} (S1761RawDescentHom X Y) :=
  inferInstance

instance {U R : Scheme.{u}} (s t : R ⟶ U) : Category.{u} (S1761RawDescent s t) where
  Hom X Y := S1761RawDescentHom X Y
  id X := ⟨𝟙 _, by simp⟩
  comp {X Y Z} f g := ⟨f.f ≫ g.f, by
    calc
      (Over.pullback s).map (f.f ≫ g.f) ≫ Z.φ.hom
          = ((Over.pullback s).map f.f ≫ (Over.pullback s).map g.f) ≫ Z.φ.hom := by
              rw [Functor.map_comp]
      _ = (Over.pullback s).map f.f ≫ ((Over.pullback s).map g.f ≫ Z.φ.hom) := by
              rw [Category.assoc]
      _ = (Over.pullback s).map f.f ≫ (Y.φ.hom ≫ (Over.pullback t).map g.f) := by
              rw [g.commutes]
      _ = ((Over.pullback s).map f.f ≫ Y.φ.hom) ≫ (Over.pullback t).map g.f := by
              rw [Category.assoc]
      _ = (X.φ.hom ≫ (Over.pullback t).map f.f) ≫ (Over.pullback t).map g.f := by
              rw [f.commutes]
      _ = X.φ.hom ≫ ((Over.pullback t).map f.f ≫ (Over.pullback t).map g.f) := by
              rw [Category.assoc]
      _ = X.φ.hom ≫ (Over.pullback t).map (f.f ≫ g.f) := by
              rw [Functor.map_comp]⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp only [Category.assoc]

/-- The raw descent object type is small. -/
instance {U R : Scheme.{u}} (s t : R ⟶ U) : Small.{u} (S1761RawDescent s t) := by
  let f : S1761RawDescent s t →
      Σ V : S1761FiniteEtaleIndex U,
        ((Over.pullback s).obj (S1761FiniteEtaleOver U V) ≅
          (Over.pullback t).obj (S1761FiniteEtaleOver U V)) :=
    fun X => ⟨X.V, X.φ⟩
  apply small_of_injective (f := f)
  intro X Y h
  cases X; cases Y
  simp only [f, Sigma.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- **Unconditional**: the category of raw finite-etale descent data is
essentially small. -/
theorem S1761RawDescent_essentiallySmall {U R : Scheme.{u}} (s t : R ⟶ U) :
    EssentiallySmall.{u} (S1761RawDescent s t) :=
  essentiallySmall_of_small_of_locallySmall _

/-- Every full subcategory of the raw descent category is essentially small.
This is the form used by the cocycle condition: the actual descent category is
a full subcategory of the raw one, so its smallness does not require a second
cardinality argument. -/
theorem S1761RawDescentSubcategory_essentiallySmall {U R : Scheme.{u}}
    (s t : R ⟶ U) (C : S1761RawDescent s t → Prop) :
    EssentiallySmall.{u} (ObjectProperty.FullSubcategory C) :=
  essentiallySmall_of_fully_faithful (ObjectProperty.ι C)

/-- Non-vacuity of the raw descent type in the diagonal case `s = t`: the
identity isomorphism is a raw descent datum whenever there is an affine
finite-etale scheme over `U`. -/
noncomputable def S1761RawDescentId {U : Scheme.{u}} (s : U ⟶ U)
    (V : S1761FiniteEtaleIndex U) : S1761RawDescent s s :=
  ⟨V, Iso.refl ((Over.pullback s).obj (S1761FiniteEtaleOver U V))⟩

/-! ## 4. The missing atlas and descent input, and the conditional transfer -/

/-- Local surjectivity of a stack map at the level of scheme-valued points:
every point is etale-locally lifted through the map. -/
def S1761AtlasSurjective {X : EtaleStackOverField F} (U : SchemeOverField F)
    (p : Pseudofunctor.StrongTrans (S1738R U) X.fiber) : Prop :=
  ∀ (T : SchemeOverField F) (q : Pseudofunctor.StrongTrans (S1738R T) X.fiber),
    ∃ (T' : SchemeOverField F) (f : T' ⟶ T),
      Etale f.left ∧ Surjective f.left ∧
        ∃ (lift : Pseudofunctor.StrongTrans (S1738R T') (S1738R U)),
          Nonempty
            (Iso (Pseudofunctor.StrongTrans.vcomp lift p)
              (Pseudofunctor.StrongTrans.vcomp (S1738MkStrong T' T f) q))

/-- **The finite-type DM atlas interface.**  This records exactly the
geometric data used by the smallness argument: an affine finite-type etale
atlas whose self-fiber-product is again affine of finite type.  The DM
unramified-diagonal condition is not used by the cardinality argument; it is
part of the missing Mathlib definition of a DM stack (see the report). -/
structure S1761FiniteTypeDMAtlas (X : EtaleStackOverField F) where
  U : SchemeOverField F
  U_affine : IsAffine U.left
  U_locallyOfFiniteType : LocallyOfFiniteType U.hom
  point : Pseudofunctor.StrongTrans (S1761RepresentableStack U).fiber X.fiber
  point_etale : EtaleStackRepresentableMorphismProperty (fun f => Etale f) point
  point_surjective : S1761AtlasSurjective U point
  selfFiber_affine : IsAffine (point_etale.baseChange U point).pullbackScheme.left
  selfFiber_locallyOfFiniteType :
    LocallyOfFiniteType (point_etale.baseChange U point).pullbackScheme.hom

/-- The self-fiber-product scheme of an atlas. -/
noncomputable def S1761AtlasSelfFiber {X : EtaleStackOverField F}
    (A : S1761FiniteTypeDMAtlas X) : SchemeOverField F :=
  (A.point_etale.baseChange A.U A.point).pullbackScheme

/-- The first projection of the self-fiber-product. -/
noncomputable def S1761AtlasSelfFiberSource {X : EtaleStackOverField F}
    (A : S1761FiniteTypeDMAtlas X) : (S1761AtlasSelfFiber A).left ⟶ A.U.left :=
  (A.point_etale.baseChange A.U A.point).projection.left

/-- The second projection of the self-fiber-product, obtained from the
two-pullback comparison via strict 2-Yoneda. -/
noncomputable def S1761AtlasSelfFiberTarget {X : EtaleStackOverField F}
    (A : S1761FiniteTypeDMAtlas X) : (S1761AtlasSelfFiber A).left ⟶ A.U.left :=
  (S1738EvalStrong (S := S1761AtlasSelfFiber A) (T := A.U)
    (A.point_etale.baseChange A.U A.point).toSource).left

/-- **The missing atlas-descent theorem**, stated with the actual cover
category and the actual raw descent category.  The predicate `C` is intended
to be the cocycle condition of the groupoid; it is left as a parameter because
the groupoid multiplication is part of the missing stack-quotient theory. -/
def S1761AtlasDescentEquiv {X : HyperbolicOrbicurve F}
    (A : S1761FiniteTypeDMAtlas X.stack) : Prop :=
  ∃ C : S1761RawDescent (S1761AtlasSelfFiberSource A)
      (S1761AtlasSelfFiberTarget A) → Prop,
    Nonempty
      (@CategoryTheory.Equivalence (OrbicurveFiniteEtaleCover X)
        (ObjectProperty.FullSubcategory C)
        (S1728CoverCategory11 (F := F) (X := X)) inferInstance)

/-- If the atlas-descent equivalence holds, the actual cover category is
essentially small.  The cocycle subcategory is a full subcategory of the raw
descent category, which is essentially small by
`S1761RawDescent_essentiallySmall`. -/
theorem S1761Cover_essentiallySmall_of_atlasDescent
    {X : HyperbolicOrbicurve F} (A : S1761FiniteTypeDMAtlas X.stack)
    (h : S1761AtlasDescentEquiv A) :
    EssentiallySmall.{u} (OrbicurveFiniteEtaleCover X) := by
  rcases h with ⟨C, ⟨e⟩⟩
  haveI : EssentiallySmall.{u} (ObjectProperty.FullSubcategory C) :=
    essentiallySmall_of_fully_faithful (ObjectProperty.ι C)
  exact (essentiallySmall_congr e).2 inferInstance

/-- The first missing theorem, for the finite-type DM stack under
consideration: it admits a finite-type affine etale atlas with affine
finite-type self-fiber-product.  This is a predicate on a fixed stack, not a
claim that every etale stack has an atlas; it is intended to be instantiated
only for a finite-type separated DM stack (for the actual S1726 orbicurve the
identity atlas on the affine Weierstrass model is the intended witness). -/
def S1761FiniteTypeDMAtlasExistence (X : EtaleStackOverField F) : Prop :=
  Nonempty (S1761FiniteTypeDMAtlas X)

/-- The second missing theorem: for every such atlas, finite-etale covers of
the orbicurve are equivalent to the cocycle subcategory of the raw descent
category. -/
def S1761FiniteTypeDMCoverDescent (X : HyperbolicOrbicurve F) : Prop :=
  ∀ A : S1761FiniteTypeDMAtlas X.stack, S1761AtlasDescentEquiv A

/-- The target smallness statement for the actual cover category. -/
def S1761FiniteTypeDMCoverSmallness (X : HyperbolicOrbicurve F) : Prop :=
  EssentiallySmall.{u} (OrbicurveFiniteEtaleCover X)

/-- **The exact reduction**: the two named geometric theorems imply the
cardinality bound for the orbicurve cover category. -/
theorem S1761FiniteTypeDMCoverSmallness_of_inputs
    {X : HyperbolicOrbicurve F}
    (hA : S1761FiniteTypeDMAtlasExistence X.stack)
    (hD : S1761FiniteTypeDMCoverDescent X) :
    S1761FiniteTypeDMCoverSmallness X := by
  rcases hA with ⟨A⟩
  exact S1761Cover_essentiallySmall_of_atlasDescent A (hD A)

/-! ## 5. Checks and axiom audit -/

#check S1761_affineFiniteType_essentiallySmall
#check S1761_affineField_essentiallySmall
#check S1761AffineFiniteEtaleSlice_essentiallySmall
#check S1761FieldFiniteEtale_essentiallySmall
#check S1761TwoYonedaStrong
#check S1761TwoYonedaRequired
#check S1761StrongTrans_small
#check S1761RepresentableIsStack
#check S1761RepresentableStack
#check S1761RawDescent
#check S1761RawDescentHom
#check S1761RawDescent_essentiallySmall
#check S1761RawDescentSubcategory_essentiallySmall
#check S1761RawDescentId
#check S1761AtlasSurjective
#check S1761FiniteTypeDMAtlas
#check S1761AtlasDescentEquiv
#check S1761Cover_essentiallySmall_of_atlasDescent
#check S1761FiniteTypeDMAtlasExistence
#check S1761FiniteTypeDMCoverDescent
#check S1761FiniteTypeDMCoverSmallness
#check S1761FiniteTypeDMCoverSmallness_of_inputs

#print axioms S1761_affineFiniteType_essentiallySmall
#print axioms S1761_affineField_essentiallySmall
#print axioms S1761AffineFiniteEtaleSlice_essentiallySmall
#print axioms S1761FieldFiniteEtale_essentiallySmall
#print axioms S1761TwoYonedaStrong
#print axioms S1761TwoYonedaRequired
#print axioms S1761StrongTrans_small
#print axioms S1761RepresentableIsStack
#print axioms S1761RawDescent_essentiallySmall
#print axioms S1761RawDescentSubcategory_essentiallySmall
#print axioms S1761Cover_essentiallySmall_of_atlasDescent
#print axioms S1761FiniteTypeDMCoverSmallness_of_inputs

end LeanFormal.IUT.XiFPaper.S1761DMStackSmallnessActual