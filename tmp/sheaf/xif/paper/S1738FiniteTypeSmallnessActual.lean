import Iut.Foundations.Orbicurve
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# S1738: finite-type smallness and the actual orbicurve cover category

S1728 showed that a small raw cover-map datum is a *necessary* input for the
target interface `OrbicurveEtaleFundamentalGroup`; the actual cover-map type is
`Type (u+1)` while the target asks for a `Type u` hom family.  This file
tries the finite-type route: Mathlib's

  `AlgebraicGeometry.essentiallySmall_costructuredArrow_Spec`

says that the category of affine schemes locally of finite type over a fixed
*base scheme* `Y` is essentially small.  We restate and use that theorem,
and we test whether it can prove smallness of the actual cover objects/maps of
`Iut.OrbicurveFiniteEtaleCover X`.

## Result

The scheme-level theorem is available and unconditional.  It does **not**
reach the actual cover category:

* the cover source is an `EtaleStackOverField F` (a category-valued etale
  stack), not a `Scheme`; the finite-type theorem is stated for
  `Spec R ⟶ Y` with `Y` a scheme.  No representability of the source stack
  by a scheme, and no finite-type/locally-finite-type property of such a
  representing scheme, is part of `EtaleStackOverField` or of
  `OrbicurveFiniteEtaleCover`;
* the map field is a strong transformation of pseudofunctors, whose type is
  `Type (u+1)`; even for representable source and target, compressing it to a
  scheme morphism needs the 2-Yoneda/descent equivalence
  `StrongTrans (R S) (R T) ≃ (S ⟶ T)`.  We prove the forward construction,
  its inverse on scheme morphisms, and the fact that the naturality square
  determines `app` by the single scheme morphism; the remaining equality of
  the full strong-transformation structures is recorded as
  `S1738TwoYonedaStrong`, the exact first missing lemma of the represented
  case;
* the cover object additionally stores an `EtaleStackFiniteEtaleMorphism`
  witness, whose `EtaleStackBaseChangePresentation` fields contain arbitrary
  `pullbackScheme` choices.  That witness type is not a subsingleton, so even
  after representability one needs a small (or propositional) replacement for
  it.  This is the second missing piece for the *objects*.

No `Shrink`, `ULift`, `PLift`, `sorry`, axiom, or fake skeleton is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1738FiniteTypeSmallnessActual

open Iut
open CategoryTheory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open scoped SpecOfNotation

universe u

/-! ## 1. The finite-type smallness theorem of Mathlib -/

/-- Mathlib's class `LocallyOfFiniteType`, packaged as a morphism property.
The wrapper is reducible so that the existing instances for the class remain
visible. -/
@[reducible] def S1738LocallyOfFiniteType : MorphismProperty Scheme.{u} :=
  fun ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) => LocallyOfFiniteType (X := X) (Y := Y) f

instance : MorphismProperty.RespectsIso (S1738LocallyOfFiniteType.{u}) := by
  have h : S1738LocallyOfFiniteType.{u} = affineLocally (@RingHom.FiniteType) :=
    HasRingHomProperty.eq_affineLocally _
  rw [h]
  exact affineLocally_respectsIso _ RingHom.finiteType_respectsIso

/-- The exact Mathlib input: affine schemes locally of finite type over a
fixed base scheme `Y` form an essentially small category. -/
theorem S1738_affineLocallyOfFiniteType_essentiallySmall
    (Y : Scheme.{u}) :
    EssentiallySmall.{u}
      (S1738LocallyOfFiniteType.{u}.CostructuredArrow ⊤ Scheme.Spec Y) :=
  AlgebraicGeometry.essentiallySmall_costructuredArrow_Spec
    S1738LocallyOfFiniteType.{u} le_rfl

/-- The same statement over the base field.  This is the affine finite-type
scheme cardinal bound in the precise form relevant to the orbicurve base. -/
theorem S1738_affineField_essentiallySmall
    (F' : Type u) [Field F'] :
    EssentiallySmall.{u}
      (S1738LocallyOfFiniteType.{u}.CostructuredArrow ⊤ Scheme.Spec (Spec(F'))) :=
  S1738_affineLocallyOfFiniteType_essentiallySmall (Spec(F'))

/-- The two consequences of essential smallness: the skeleton is a small type,
and the hom types are small. -/
theorem S1738_affineLocallyOfFiniteType_skeletonSmall
    (Y : Scheme.{u}) :
    Small.{u} (Skeleton
      (S1738LocallyOfFiniteType.{u}.CostructuredArrow ⊤ Scheme.Spec Y)) :=
  (essentiallySmall_iff _).1
    (S1738_affineLocallyOfFiniteType_essentiallySmall Y) |>.1

theorem S1738_affineLocallyOfFiniteType_locallySmall
    (Y : Scheme.{u}) :
    LocallySmall.{u}
      (S1738LocallyOfFiniteType.{u}.CostructuredArrow ⊤ Scheme.Spec Y) :=
  (essentiallySmall_iff _).1
    (S1738_affineLocallyOfFiniteType_essentiallySmall Y) |>.2

/-! ## 2. The actual cover types and their universe status -/

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}

/-- The actual finite-etale cover type. -/
abbrev S1738Cover (X : HyperbolicOrbicurve F) : Type (u + 1) :=
  OrbicurveFiniteEtaleCover X

/-- The actual cover-map type. -/
abbrev S1738CoverMap {X : HyperbolicOrbicurve F}
    (A B : OrbicurveFiniteEtaleCover X) : Type (u + 1) :=
  OrbicurveFiniteEtaleCoverMap A B

/-- Both the actual cover objects and the actual cover maps live one universe
above the field.  This is the obstruction isolated by S1728. -/
theorem S1738Cover_smallSucc (X : HyperbolicOrbicurve F) :
    Small.{u + 1} (S1738Cover X) :=
  small_self _

theorem S1738CoverMap_smallSucc {X : HyperbolicOrbicurve F}
    (A B : OrbicurveFiniteEtaleCover X) :
    Small.{u + 1} (S1738CoverMap A B) :=
  small_self _

/-- The exact target-universe smallness statement: every actual cover-map
type must be equivalent to a `Type u` carrier. -/
def S1738CoverHomsSmall (X : HyperbolicOrbicurve F) : Prop :=
  ∀ A B : OrbicurveFiniteEtaleCover X, Small.{u} (S1738CoverMap A B)

/-- S1728's small raw cover-map datum, restated as a Sigma type. -/
abbrev S1738RawCoverData {X : HyperbolicOrbicurve F}
    (A B : OrbicurveFiniteEtaleCover X) : Type (u + 1) :=
  Σ (Carrier : Type u), Carrier ≃ S1738CoverMap A B

/-- S1728's requirement is exactly `Small.{u}` of the actual cover-map
type. -/
theorem S1738RawCoverData_nonempty_iff_small {X : HyperbolicOrbicurve F}
    (A B : OrbicurveFiniteEtaleCover X) :
    Nonempty (S1738RawCoverData A B) ↔
      Small.{u} (S1738CoverMap A B) := by
  constructor
  · rintro ⟨⟨Carrier, e⟩⟩
    exact Small.mk' e.symm
  · intro h
    obtain ⟨S, ⟨e⟩⟩ := h.equiv_small
    exact ⟨⟨S, e.symm⟩⟩

/-- The equivalent form of the necessary small raw cover data. -/
def S1738RawCoverDataRequired (X : HyperbolicOrbicurve F) : Prop :=
  ∀ A B : OrbicurveFiniteEtaleCover X,
    Nonempty (S1738RawCoverData A B)

theorem S1738RawCoverDataRequired_iff (X : HyperbolicOrbicurve F) :
    S1738RawCoverDataRequired X ↔ S1738CoverHomsSmall X := by
  constructor
  · intro h A B
    exact (S1738RawCoverData_nonempty_iff_small A B).1 (h A B)
  · intro h A B
    exact (S1738RawCoverData_nonempty_iff_small A B).2 (h A B)

/-! ## 3. Representable source/target: the partial 2-Yoneda computation -/

/-- The representable etale stack attached to a scheme. -/
abbrev S1738R (S : SchemeOverField F) : EtaleStackPseudofunctor F :=
  schemeRepresentableEtalePseudofunctor F S

@[simp] theorem S1738R_obj (S : SchemeOverField F)
    (U : (SchemeOverField F)ᵒᵖ) :
    (S1738R S).obj (LocallyDiscrete.mk U) =
      Cat.of (Discrete (Opposite.unop U ⟶ S)) :=
  rfl

@[simp] theorem S1738R_map_obj_as (S : SchemeOverField F)
    {a b : LocallyDiscrete (SchemeOverField F)ᵒᵖ} (f : a ⟶ b)
    (g : Discrete (a.as.unop ⟶ S)) :
    (((S1738R S).map f).toFunctor.obj g).as = f.as.unop ≫ g.as :=
  rfl

/-- The hom-category of two projected representable stacks is thin.  This is
the formal reason why all coherence data of a strong transformation between
represented stacks is a subsingleton. -/
theorem S1738R_hom₂_subsingleton (S T : SchemeOverField F)
    {a b : LocallyDiscrete (SchemeOverField F)ᵒᵖ}
    (phi psi : (S1738R S).obj a ⟶ (S1738R T).obj b) :
    Subsingleton (phi ⟶ psi) := by
  haveI : IsDiscrete (↑((S1738R T).obj b)) := by
    change IsDiscrete (Discrete (Opposite.unop b.as ⟶ T))
    infer_instance
  constructor
  intro alpha beta
  apply Cat.Hom₂.ext
  ext x
  exact Subsingleton.elim _ _

/-- Evaluation at the identity of the source: the only piece of a strong
transformation between represented stacks that survives the discrete Yoneda
computation. -/
def S1738EvalStrong (S T : SchemeOverField F)
    (eta : Pseudofunctor.StrongTrans (S1738R S) (S1738R T)) :
    (S ⟶ T) :=
  (((eta.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
    (Discrete.mk (𝟙 S))).as)

/-- The backward construction: a morphism of representing schemes yields a
strong transformation of represented stacks. -/
noncomputable def S1738MkStrong (S T : SchemeOverField F) (x : S ⟶ T) :
    Pseudofunctor.StrongTrans (S1738R S) (S1738R T) where
  app a :=
    (Discrete.functor (fun g : a.as.unop ⟶ S => Discrete.mk (g ≫ x))).toCatHom
  naturality {a b} f := by
    refine Cat.Hom.isoMk (Discrete.natIso
      (fun g : Discrete (a.as.unop ⟶ S) => ?_))
    exact Discrete.eqToIso (by simp)
  naturality_naturality := by
    intros
    exact (S1738R_hom₂_subsingleton S T _ _).elim _ _
  naturality_id := by
    intros
    exact (S1738R_hom₂_subsingleton S T _ _).elim _ _
  naturality_comp := by
    intros
    exact (S1738R_hom₂_subsingleton S T _ _).elim _ _

@[simp] theorem S1738EvalStrong_mkStrong (S T : SchemeOverField F) (x : S ⟶ T) :
    S1738EvalStrong S T (S1738MkStrong S T x) = x := by
  simp [S1738EvalStrong, S1738MkStrong]

/-- Naturality determines the value of the strong transformation at every
test scheme from the single scheme morphism `S1738EvalStrong eta`.  This is
the genuine (unconditional) part of the 2-Yoneda computation. -/
theorem S1738_app_eq_of_eval (S T : SchemeOverField F)
    (eta : Pseudofunctor.StrongTrans (S1738R S) (S1738R T))
    {a : LocallyDiscrete (SchemeOverField F)ᵒᵖ} (g : a.as.unop ⟶ S) :
    (((eta.app a).toFunctor.obj (Discrete.mk g)).as) =
      g ≫ S1738EvalStrong S T eta := by
  let f : (LocallyDiscrete.mk (Opposite.op S)) ⟶ a :=
    Quiver.Hom.toLoc (Opposite.op g)
  have hf : f.as = Opposite.op g := rfl
  have hnat := eta.naturality f
  let e := Cat.Hom.toNatIso hnat
  have h := Discrete.eq_of_hom (e.hom.app (Discrete.mk (𝟙 S)))
  simp only [e, Cat.Hom₂.toNatTrans, CategoryStruct.comp,
    Functor.toCatHom, Functor.comp_obj, S1738R_map_obj_as, S1738R_obj, hf,
    S1738EvalStrong, Category.id_comp] at h
  exact h

/-- Consequently two strong transformations with the same evaluating scheme
morphism have the same `app` data at every test object. -/
theorem S1738_app_eq_of_eval_eq (S T : SchemeOverField F)
    {eta1 eta2 : Pseudofunctor.StrongTrans (S1738R S) (S1738R T)}
    (h : S1738EvalStrong S T eta1 = S1738EvalStrong S T eta2)
    {a : LocallyDiscrete (SchemeOverField F)ᵒᵖ} (g : a.as.unop ⟶ S) :
    (((eta1.app a).toFunctor.obj (Discrete.mk g)).as) =
      (((eta2.app a).toFunctor.obj (Discrete.mk g)).as) := by
  rw [S1738_app_eq_of_eval S T eta1 g,
    S1738_app_eq_of_eval S T eta2 g, h]

/-- The exact first missing lemma in the represented source/target case: the
full strong-transformation structure is determined by its evaluating scheme
morphism.  This is the 2-Yoneda/descent statement for the etale stack
`S1738R T`; Mathlib provides the stack descent API but not this form of the
2-Yoneda equivalence. -/
def S1738TwoYonedaStrong (S T : SchemeOverField F) : Prop :=
  ∀ eta : Pseudofunctor.StrongTrans (S1738R S) (S1738R T),
    eta = S1738MkStrong S T (S1738EvalStrong S T eta)

/-- If the first missing lemma holds, the strong-transformation type of two
represented stacks is small at the base universe (a surjection from the
`Type u` scheme-hom type). -/
theorem S1738StrongTrans_small_of_twoYoneda (S T : SchemeOverField F)
    (h : S1738TwoYonedaStrong S T) :
    Small.{u} (Pseudofunctor.StrongTrans (S1738R S) (S1738R T)) := by
  haveI : Small.{u} (S ⟶ T) := small_self _
  exact small_of_surjective (f := S1738MkStrong S T)
    (fun eta => ⟨S1738EvalStrong S T eta, (h eta).symm⟩)

/-! ## 4. The precise missing input for the actual cover category -/

/-- A weak isomorphism of etale stacks, expressed with strong transformations
and 2-isomorphisms of strong transformations.  This is the representation
relation needed to compare an actual cover source with a represented stack. -/
structure S1738FiberIso (P Q : EtaleStackPseudofunctor F) where
  forward : Pseudofunctor.StrongTrans P Q
  backward : Pseudofunctor.StrongTrans Q P
  forward_backward : Nonempty
    (Iso (Pseudofunctor.StrongTrans.vcomp forward backward)
      (Pseudofunctor.StrongTrans.id P))
  backward_forward : Nonempty
    (Iso (Pseudofunctor.StrongTrans.vcomp backward forward)
      (Pseudofunctor.StrongTrans.id Q))

/-- A scheme chart of an actual cover source: the source stack is isomorphic
to the representable stack of an affine scheme locally of finite type over the
field. -/
structure S1738SourceSchemeChart {X : HyperbolicOrbicurve F}
    (A : OrbicurveFiniteEtaleCover X) where
  scheme : SchemeOverField F
  affine : IsAffine scheme.left
  locallyOfFiniteType : LocallyOfFiniteType scheme.hom
  represented : S1738FiberIso A.source.fiber (S1738R scheme)

/-- A scheme chart of the target orbicurve stack. -/
structure S1738TargetSchemeChart (X : HyperbolicOrbicurve F) where
  scheme : SchemeOverField F
  represented : S1738FiberIso X.stack.fiber (S1738R scheme)

/-- **First missing (representability and finite type of the source).**
Every finite-etale cover source must be representable by an affine scheme of
locally finite type over the field, and the target orbicurve stack must itself
be representable by a scheme.  None of this follows from
`EtaleStackOverField F`; note in particular that finite-etale covers of a
stacky orbicurve need not be schemes. -/
def S1738SourceRepresentabilityRequired (X : HyperbolicOrbicurve F) : Prop :=
  (Nonempty (S1738TargetSchemeChart X)) ∧
    (∀ A : OrbicurveFiniteEtaleCover X,
      Nonempty (S1738SourceSchemeChart A))

/-- **Second missing (2-Yoneda/descent for represented stacks).**  This is the
`S1738TwoYonedaStrong` family; it is what turns the large strong-transformation
type into the small scheme-hom type. -/
def S1738TwoYonedaRequired : Prop :=
  ∀ S T : SchemeOverField F, S1738TwoYonedaStrong S T

/-- **Third missing (the finite-etale witness).**  The actual cover object
stores an `EtaleStackFiniteEtaleMorphism` structure whose
`EtaleStackBaseChangePresentation` fields contain arbitrary
`pullbackScheme` choices.  A small replacement for this witness (or a proof
that the witness type is essentially small) is needed for smallness of the
*objects*, separately from the smallness of the homs. -/
structure S1738FiniteEtaleWitnessCompression {X : HyperbolicOrbicurve F}
    (A : OrbicurveFiniteEtaleCover X) where
  Carrier : Type u
  equiv : Carrier ≃ EtaleStackFiniteEtaleMorphism A.map

/-- The three missing inputs, bundled.  This is the precise reduction target
for any finite-type-based proof of the S1728 small raw cover data. -/
def S1738FiniteTypeRouteRequired (X : HyperbolicOrbicurve F) : Prop :=
  S1738SourceRepresentabilityRequired X ∧
    S1738TwoYonedaRequired (F := F) ∧
      (∀ A : OrbicurveFiniteEtaleCover X,
        Nonempty (S1738FiniteEtaleWitnessCompression A))

/-- The finite-type scheme bound is available only at the scheme level; this
is the exact gap between the Mathlib theorem and the actual cover source. -/
theorem S1738_schemeLevelAvailable (Y : Scheme.{u}) :
    EssentiallySmall.{u}
      (S1738LocallyOfFiniteType.{u}.CostructuredArrow ⊤ Scheme.Spec Y) :=
  S1738_affineLocallyOfFiniteType_essentiallySmall Y

/-! ## 5. Checks -/

#check S1738_affineLocallyOfFiniteType_essentiallySmall
#check S1738_affineField_essentiallySmall
#check S1738_affineLocallyOfFiniteType_skeletonSmall
#check S1738_affineLocallyOfFiniteType_locallySmall
#check S1738Cover
#check S1738CoverMap
#check S1738Cover_smallSucc
#check S1738CoverMap_smallSucc
#check S1738CoverHomsSmall
#check S1738RawCoverData
#check S1738RawCoverData_nonempty_iff_small
#check S1738RawCoverDataRequired
#check S1738RawCoverDataRequired_iff
#check S1738EvalStrong
#check S1738MkStrong
#check S1738EvalStrong_mkStrong
#check S1738_app_eq_of_eval
#check S1738_app_eq_of_eval_eq
#check S1738TwoYonedaStrong
#check S1738StrongTrans_small_of_twoYoneda
#check S1738FiberIso
#check S1738SourceSchemeChart
#check S1738TargetSchemeChart
#check S1738SourceRepresentabilityRequired
#check S1738TwoYonedaRequired
#check S1738FiniteEtaleWitnessCompression
#check S1738FiniteTypeRouteRequired
#check S1738_schemeLevelAvailable

#print axioms S1738_affineLocallyOfFiniteType_essentiallySmall
#print axioms S1738_affineField_essentiallySmall
#print axioms S1738EvalStrong_mkStrong
#print axioms S1738_app_eq_of_eval
#print axioms S1738StrongTrans_small_of_twoYoneda
#print axioms S1738RawCoverDataRequired_iff

end LeanFormal.IUT.XiFPaper.S1738FiniteTypeSmallnessActual
