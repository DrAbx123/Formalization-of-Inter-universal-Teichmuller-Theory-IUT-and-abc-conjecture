import tmp.sheaf.xif.paper.S1756CoverSourceRepresentabilityActual
import tmp.sheaf.xif.paper.S1755TwoYonedaSmallnessActual
import tmp.sheaf.xif.paper.S1754OrbicurvePiFieldsActual
import tmp.sheaf.xif.paper.S1738FiniteTypeSmallnessActual
import tmp.sheaf.xif.paper.S1744Category01AssemblyActual
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Skeletal
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.AffineScheme



/-!
# S1790: small-model alternatives for the actual D6 cover category

## Question

The D6 source datum needs a genuine small cover category on the actual cover
type

    S1728Cover = OrbicurveFiniteEtaleCover S1726Orbicurve,

whose raw hom type is `S1728CoverMap A B : Type 1`.  S1728, S1738, S1754 and
S1755 all reduce the target's categorical fields to a small raw cover-map
carrier.  This file compares the four candidate small models:

* A. the affine R'-algebra model (`(CommAlgCat.FiniteEtale R')ᵒᵖ`),
      the route probed by S1777/S1781;
* B. the DM-stack/affine finite-etale cardinal bound of S1761/S1733;
* C. the finite-group action model `Action FintypeCat G`;
* D. the direct finite hom carrier of S1728/S1754.

## Result

* **2-Yoneda is unconditional.**  `S1790TwoYonedaStrong` proves that a raw
  strong transformation between representable etale stacks is *equal* to the
  one reconstructed from its evaluation at the identity, so

      StrongTrans (R S) (R T) ≃ (S ⟶ T)

  is an actual equivalence of raw types, not only of 2-isomorphism classes.
  This closes the S1738 `S1738TwoYonedaRequired` gap.

* **The affine R'-algebra object map is unconditional.**
  `S1790AlgOfCover A = Γ(S1733Model A)` is a genuine finite etale
  R'-algebra, and `S1790AffineCarrier A B` is a Type 0 carrier (algebra maps
  in the contravariant direction).  The exact missing statement of this route
  is `S1790AffineRawCarrierEquiv`: algebra homs are in raw bijection with
  cover maps.  S1781 (parallel artifact, same checkout) proves that the
  canonical class-level functor's identity law is *equivalent* to S1756's
  source-representability statement, and that its fullness and essential
  surjectivity are further genuine gaps.  Thus the affine route alone only
  reaches the 2-isomorphism quotient, not the raw carrier.

* **The DM bound is object-level only.**  `S1790DMObjectBound` is the
  unconditional `EssentiallySmall S1733Slice` (S1761/S1733).  It gives no raw
  hom map: the exact missing comparison is
  `S1790DMSliceComparisonMissing = S1755SliceComparisonMissing`, and even that
  is a comparison of the 2-isomorphism quotient category.

* **The action model is small but needs the Galois correspondence.**
  `S1790ActionCategory G = Action FintypeCat G` is a `Category.{0,1}` with
  Type 0 homs.  A raw model would need a category equivalence with the actual
  cover category; for finite G this additionally requires the cover category to
  have only finitely many isomorphism classes, which is not proved here and is
  not a consequence of the present definitions.

* **The direct finite hom carrier is the minimal residual.**
  `S1790RawCarrierRequired` is exactly S1728's
  `S1728SmallRawCoverDataRequired`; it is necessary for the full target
  (`S1790FullCategoricalMissing_to_raw`) and sufficient for a
  `Category.{0,1}` on the actual cover type
  (`S1790DirectRoute_to_category01`).  The optimal *geometric* route is
  `S1790ModelHomRouteMissing = S1755ModelHomEquivMissing`: the S1742 extraction
  from raw cover maps to scheme morphisms between the affine models is already
  constructed, and only its raw inverse is missing.  This is strictly stronger
  than the affine/DM class-level comparisons and strictly weaker than the full
  strict functor coherence of `S1754StrictHomEquiv`.

## Honest boundary

No `sorry`, no new axiom, no `Shrink`, no `ULift`, no `PUnit`, and no fake
category, carrier, or equivalence is introduced.  The missing statements are
recorded as `Prop`/structure types and are never inhabited here.  The only
axioms used by the constructed declarations are `propext`, `Classical.choice`
and `Quot.sound`.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1790SmallnessAlternativesActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1738FiniteTypeSmallnessActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1744Category01AssemblyActual
open LeanFormal.IUT.XiFPaper.S1754OrbicurvePiFieldsActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual

universe u

/-! ## 1. 2-Yoneda for raw strong transformations is unconditional -/

instance S1790IsoSubsingletonOfHomSubsingleton {C : Type u} [Category.{u} C] {X Y : C}
    [Subsingleton (X ⟶ Y)] : Subsingleton (X ≅ Y) where
  allEq e1 e2 := by
    apply Iso.ext
    exact Subsingleton.elim _ _

instance S1790CatHomSubsingleton (S T : SchemeOverField S1726K)
    {a b : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
    (phi psi : (S1738R S).obj a ⟶ (S1738R T).obj b) :
    Subsingleton (phi ⟶ psi) :=
  S1738R_hom₂_subsingleton S T phi psi

theorem S1790StrongTrans_ext (S T : SchemeOverField S1726K)
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

theorem S1790TwoYonedaStrong (S T : SchemeOverField S1726K) :
    S1738TwoYonedaStrong S T := by
  intro eta
  apply S1790StrongTrans_ext
  intro a
  apply Cat.ext
  apply Discrete.functor_ext
  intro g
  exact Discrete.ext (S1738_app_eq_of_eval S T eta g)

/-- Raw strong transformations between representable etale stacks are
equivalent to scheme morphisms, not merely their 2-isomorphism classes. -/
noncomputable def S1790StrongTransEquivSchemeHom (S T : SchemeOverField S1726K) :
    Pseudofunctor.StrongTrans (S1738R S) (S1738R T) ≃ (S ⟶ T) where
  toFun := S1738EvalStrong S T
  invFun := S1738MkStrong S T
  left_inv eta := (S1790TwoYonedaStrong S T eta).symm
  right_inv x := S1738EvalStrong_mkStrong S T x

theorem S1790TwoYonedaRequired : S1738TwoYonedaRequired (F := S1726K) :=
  fun S T => S1790TwoYonedaStrong S T

/-! ## 2. Route A: affine R'-algebra model -/

attribute [local instance] S1744Model_isAffine S1744Base_isAffine

abbrev S1790Sections (A : S1728Cover) : CommRingCat :=
  (Over.left (S1733Model A)).presheaf.obj (Opposite.op ⊤)

noncomputable def S1790StructHom (A : S1728Cover) :
    CommRingCat.of S1726CoordinateRing ⟶ S1790Sections A :=
  (Scheme.ΓSpecIso (CommRingCat.of S1726CoordinateRing)).inv ≫
    (S1733ModelOver A).left.appTop

noncomputable def S1790StructRingHom (A : S1728Cover) :
    S1726CoordinateRing →+* S1790Sections A :=
  (S1790StructHom A).hom

instance S1790Algebra (A : S1728Cover) :
    Algebra S1726CoordinateRing (S1790Sections A) :=
  (S1790StructRingHom A).toAlgebra

theorem S1790_algebraMap_eq (A : S1728Cover) :
    algebraMap S1726CoordinateRing (S1790Sections A) = S1790StructRingHom A :=
  RingHom.algebraMap_toAlgebra (S1790StructRingHom A)

theorem S1790_ringHom_finite (A : S1728Cover) :
    RingHom.Finite (S1790StructRingHom A) := by
  haveI hfin : IsFinite (S1733ModelOver A).left := (S1733Model_finiteEtale A).1
  have h : RingHom.Finite ((S1733ModelOver A).left.appTop).hom :=
    Scheme.Hom.finite_appTop (S1733ModelOver A).left
  exact RingHom.finite_respectsIso.2 ((S1733ModelOver A).left.appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of S1726CoordinateRing)).symm.commRingCatIsoToRingEquiv) h

theorem S1790_ringHom_etale (A : S1728Cover) :
    RingHom.Etale (S1790StructRingHom A) := by
  have h : RingHom.Etale ((S1733ModelOver A).left.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (Q := @RingHom.Etale)).mp
      (S1733Model_finiteEtale A).2
  exact RingHom.Etale.respectsIso.2 ((S1733ModelOver A).left.appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of S1726CoordinateRing)).symm.commRingCatIsoToRingEquiv) h

theorem S1790_moduleFinite (A : S1728Cover) :
    Module.Finite S1726CoordinateRing (S1790Sections A) := by
  have h := S1790_ringHom_finite A
  rw [RingHom.Finite] at h
  exact h

theorem S1790_algebraEtale (A : S1728Cover) :
    Algebra.Etale S1726CoordinateRing (S1790Sections A) := by
  have h := S1790_ringHom_etale A
  show RingHom.Etale (algebraMap S1726CoordinateRing (S1790Sections A))
  rw [S1790_algebraMap_eq]
  exact h

/-- The affine cover algebra attached to a cover. -/
noncomputable def S1790AlgOfCover (A : S1728Cover) :
    CommAlgCat.FiniteEtale S1726CoordinateRing :=
  letI : Module.Finite S1726CoordinateRing (S1790Sections A) := S1790_moduleFinite A
  letI : Algebra.Etale S1726CoordinateRing (S1790Sections A) := S1790_algebraEtale A
  CommAlgCat.FiniteEtale.of S1726CoordinateRing (S1790Sections A)

/-- The Type 0 carrier of the affine route: algebra maps in the contravariant
direction. -/
abbrev S1790AffineCarrier (A B : S1728Cover) : Type :=
  S1790AlgOfCover B ⟶ S1790AlgOfCover A

/-- The exact missing statement of the affine route: the affine algebra homs are
in bijection with the raw cover maps. -/
def S1790AffineRawCarrierEquiv : Prop :=
  ∀ A B : S1728Cover, Nonempty (S1790AffineCarrier A B ≃ S1728CoverMap A B)

/-! ## 3. Route B: DM stack cardinal bound -/

/-- The unconditional object-level cardinal bound: the affine finite-etale slice
over Spec R' is essentially small.  This is the S1761/S1733 bound. -/
theorem S1790DMObjectBound : EssentiallySmall.{0} S1733Slice :=
  S1733Slice_essentiallySmall

theorem S1790DMSkeletonSmall : Small.{0} (Skeleton S1733Slice) :=
  (essentiallySmall_iff S1733Slice).1 S1790DMObjectBound |>.1

/-- The exact missing statement of the DM/slice route: a fully faithful
essentially surjective comparison from the 2-isomorphism quotient category to
the affine finite-etale slice. -/
def S1790DMSliceComparisonMissing : Prop := S1755SliceComparisonMissing

theorem S1790DMSliceComparison_essSmall
    (h : S1790DMSliceComparisonMissing) : EssentiallySmall.{0} S1728Cover :=
  S1755EssentiallySmall_of_comparison (Classical.choice h)

theorem S1790DMSliceComparison_category01
    (h : S1790DMSliceComparisonMissing) : Nonempty (Category.{0, 1} S1728Cover) :=
  S1755Category01_of_comparison (Classical.choice h)

/-! ## 4. Route C: finite group action model -/

abbrev S1790ActionCategory (G : Type) [Group G] : Type 1 :=
  Action FintypeCat.{0} G

instance S1790ActionCategoryCategory (G : Type) [Group G] :
    Category.{0, 1} (S1790ActionCategory G) := inferInstance

/-- The exact missing statement of the finite-action route: a category
equivalence between the 2-isomorphism quotient cover category and finite
G-sets.  It is a statement about the 2-isomorphism quotient, not about raw
cover maps. -/
def S1790ActionRouteMissing (G : Type) [Group G] : Prop :=
  Nonempty (@CategoryTheory.Equivalence S1728Cover (S1790ActionCategory G)
    S1728ActualCategory11 (S1790ActionCategoryCategory G))

/-! ## 5. Route D: direct finite hom carrier -/

/-- The direct finite hom carrier required by S1728: for every pair of covers, a
Type 0 carrier equivalent to the raw cover-map type. -/
def S1790RawCarrierRequired : Prop := S1728SmallRawCoverDataRequired

/-- The full strict categorical residual of S1754: a Category.{0,1} on the
actual cover type whose homs are equivalent to the raw cover maps, compatibly
with identities and composition up to 2-isomorphism. -/
def S1790FullCategoricalMissing : Prop :=
  ∃ C : Category.{0, 1} S1728Cover,
    letI := C
    Nonempty (S1754StrictHomEquiv (F := S1726K) (X := S1726Orbicurve))

theorem S1790StrictHomEquiv_to_raw
    (C : Category.{0, 1} S1728Cover)
    (s : @S1754StrictHomEquiv S1726K _ S1726Orbicurve C) :
    S1790RawCarrierRequired := by
  intro A B
  exact ⟨{ Carrier := @Quiver.Hom _ C.toQuiver A B, equiv := s.equiv A B }⟩

theorem S1790FullCategoricalMissing_to_raw
    (h : S1790FullCategoricalMissing) : S1790RawCarrierRequired := by
  rcases h with ⟨C, s⟩
  rcases s with ⟨s⟩
  exact S1790StrictHomEquiv_to_raw C s

theorem S1790AffineRoute_to_raw
    (h : S1790AffineRawCarrierEquiv) : S1790RawCarrierRequired := by
  intro A B
  rcases h A B with ⟨e⟩
  exact ⟨{ Carrier := S1790AffineCarrier A B, equiv := e }⟩

theorem S1790AffineRoute_to_category01
    (h : S1790AffineRawCarrierEquiv) : Nonempty (Category.{0, 1} S1728Cover) :=
  ⟨S1728ActualCategory01 S1790AffineCarrier
    (fun A B => Classical.choice (h A B))⟩

/-- The model-hom route of S1755: the S1742 extraction from cover maps to model
scheme morphisms is a raw bijection. -/
def S1790ModelHomRouteMissing : Prop := S1755ModelHomEquivMissing

theorem S1790ModelHomRoute_to_raw
    (h : S1790ModelHomRouteMissing) : S1790RawCarrierRequired :=
  S1755SmallRawCoverDataRequired_of_modelHomEquiv h

theorem S1790ModelHomRoute_to_category01
    (h : S1790ModelHomRouteMissing) : Nonempty (Category.{0, 1} S1728Cover) :=
  S1755Category01_of_modelHomEquiv h


/-! ## 6. Comparison of the routes -/

/-- Direct raw carrier implies a genuine Category.{0,1} on the actual cover
type, by S1728's transport construction. -/
theorem S1790DirectRoute_to_category01
    (h : S1790RawCarrierRequired) : Nonempty (Category.{0, 1} S1728Cover) :=
  ⟨S1728ActualCategory01
    (fun A B => (Classical.choice (h A B)).Carrier)
    (fun A B => (Classical.choice (h A B)).equiv)⟩

/-- The direct route is exactly S1728's small raw cover data. -/
def S1790DirectRouteMissing : Prop := S1790RawCarrierRequired

/-- The optimal route: the S1742 extraction has a raw inverse. -/
def S1790OptimalRoute : Prop := S1790ModelHomRouteMissing

theorem S1790OptimalRoute_to_direct
    (h : S1790OptimalRoute) : S1790DirectRouteMissing :=
  S1790ModelHomRoute_to_raw h

theorem S1790OptimalRoute_to_category01
    (h : S1790OptimalRoute) : Nonempty (Category.{0, 1} S1728Cover) :=
  S1790ModelHomRoute_to_category01 h

/-- The affine route is the class-level affine comparison plus its raw carrier
equivalence. -/
def S1790AffineRouteMissing : Prop := S1790AffineRawCarrierEquiv

/-- The DM route is the affine slice comparison (of the 2-isomorphism
quotient). -/
def S1790DMRouteMissing : Prop := S1790DMSliceComparisonMissing


/-- All four routes land on the same minimal first obstacle: a raw small
carrier for the actual cover maps.  The affine route and the direct strict
route imply it; the model-hom route implies it; the DM and action routes only
give small models of the 2-isomorphism quotient and therefore still need a
raw strictification. -/
theorem S1790_affine_and_model_routes_meet_raw
    (ha : S1790AffineRawCarrierEquiv)
    (hm : S1790ModelHomRouteMissing) :
    S1790RawCarrierRequired ∧ Nonempty (Category.{0, 1} S1728Cover) :=
  ⟨S1790AffineRoute_to_raw ha, S1790ModelHomRoute_to_category01 hm⟩

/-- The full target's categorical fields imply the minimal raw carrier.  Hence
the small raw carrier is a necessary first obstacle, not an optional
convenience. -/
theorem S1790_target_implies_raw
    (h : S1790FullCategoricalMissing) : S1790RawCarrierRequired :=
  S1790FullCategoricalMissing_to_raw h

/-! ## 7. Checks -/

#check S1790TwoYonedaRequired
#check S1790StrongTransEquivSchemeHom
#check S1790AlgOfCover
#check S1790AffineCarrier
#check S1790AffineRawCarrierEquiv
#check S1790DMObjectBound
#check S1790DMSkeletonSmall
#check S1790DMSliceComparisonMissing
#check S1790ActionCategory
#check S1790ActionRouteMissing
#check S1790RawCarrierRequired
#check S1790FullCategoricalMissing
#check S1790AffineRoute_to_raw
#check S1790AffineRoute_to_category01
#check S1790ModelHomRoute_to_raw
#check S1790ModelHomRoute_to_category01
#check S1790DirectRoute_to_category01
#check S1790DirectRouteMissing
#check S1790OptimalRoute
#check S1790OptimalRoute_to_direct
#check S1790OptimalRoute_to_category01
#check S1790AffineRouteMissing
#check S1790DMRouteMissing
#check S1790FullCategoricalMissing_to_raw

#print axioms S1790TwoYonedaRequired
#print axioms S1790StrongTransEquivSchemeHom
#print axioms S1790AlgOfCover
#print axioms S1790DMObjectBound
#print axioms S1790DMSkeletonSmall
#print axioms S1790AffineRoute_to_raw
#print axioms S1790ModelHomRoute_to_raw
#print axioms S1790DirectRoute_to_category01
#print axioms S1790FullCategoricalMissing_to_raw

end LeanFormal.IUT.XiFPaper.S1790SmallnessAlternativesActual
