/-
# S1736: PreGaloisCategory / GaloisCategory on the actual orbicurve cover type

## Scope

The target object is the actual type

  Iut.OrbicurveFiniteEtaleCover X

of representable finite-etale stack maps to a hyperbolic orbicurve X.
S1728 constructed a genuine Category.{1,1} on this type by quotienting the
actual cover maps by 2-isomorphism.  The present file checks Mathlib's
PreGaloisCategory fields against that actual category, records the exact
missing construction for each field, and constructs the target-universe
GaloisCategory conditionally on the small-Hom input and the missing
PreGalois/fiber-functor data.

## Mathlib field audit (verbatim from Mathlib.CategoryTheory.Galois.Basic)

PreGaloisCategory C has exactly five fields:

1. hasTerminal : HasTerminal C;
2. hasPullbacks : HasPullbacks C;
3. hasFiniteCoproducts : HasFiniteCoproducts C;
4. hasQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
     HasColimitsOfShape (SingleObj G) C;
5. monoInducesIsoOnDirectSummand {X Y : C} (i : X ⟶ Y) [Mono i] :
     ∃ (Z : C) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)).

FiberFunctor F has exactly six fields: preservation of the terminal shape,
of pullbacks, of finite coproducts, of epimorphisms, of quotients by finite
groups, and reflection of isomorphisms.  GaloisCategory C extends
PreGaloisCategory C by a fiber functor to FintypeCat.{u₂}.

## Universe finding

PreGaloisCategory is NOT restricted to Category.{0}.  It is declared as
class PreGaloisCategory (C : Type u₁) [Category.{u₂, u₁} C] : Prop, so the
hom universe u₂ is arbitrary.  The actual S1728 category is
Category.{u+1, u+1} on OrbicurveFiniteEtaleCover X, and the class can be
stated there without any small-Hom hypothesis.

The literal target field of Iut.OrbicurveEtaleFundamentalGroup is different:
for F : Type u it stores coverCategory : Category.{u} (OrbicurveFiniteEtaleCover X),
i.e. Category.{0,1} when u = 0, with Type-0 homs.  S1728 proved that the
actual cover-map type is Type 1, so this is a genuine extra smallness input.
S1728's S1728ActualCategory01 constructs that category from an explicit
small carrier family.  This file treats Category.{0,1} as a hard prerequisite
of the literal target and constructs GaloisCategory.{1,0} conditionally on it.

## Honest status

* The actual Category.{1,1} is imported from S1728 (genuine, no fake).
* The terminal field is conditionally constructed from the single missing
  geometric fact that the identity cover is finite etale.
* The other four PreGalois fields and the fiber functor are recorded as exact
  missing propositions.  No inhabitant, no axiom, no sorry is supplied.
* The small-Hom family, PreGaloisCategory at the target universe, and the
  fiber functor are taken as explicit hypotheses in the target construction.
-/

import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.EssentialImage

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual

open CategoryTheory
open CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open scoped Pseudofunctor.StrongTrans

universe u v

/-! ## 0. Mathlib field audit -/

-- The class is universe-polymorphic; no Category.{0} restriction.
#check @PreGaloisCategory
#check @GaloisCategory
#check PreGaloisCategory.hasTerminal
#check PreGaloisCategory.hasPullbacks
#check PreGaloisCategory.hasFiniteCoproducts
#check PreGaloisCategory.hasQuotientsByFiniteGroups
#check PreGaloisCategory.monoInducesIsoOnDirectSummand
#check @PreGaloisCategory.FiberFunctor
#check PreGaloisCategory.FiberFunctor.preservesTerminalObjects
#check PreGaloisCategory.FiberFunctor.preservesPullbacks
#check PreGaloisCategory.FiberFunctor.preservesFiniteCoproducts
#check PreGaloisCategory.FiberFunctor.preservesEpis
#check PreGaloisCategory.FiberFunctor.preservesQuotientsByFiniteGroups
#check PreGaloisCategory.FiberFunctor.reflectsIsos
#check GaloisCategory.hasFiberFunctor

/-! ## 1. Exact field decomposition of PreGaloisCategory -/

/-- Mathlib's five PreGaloisCategory fields, grouped as in the task:
finite limits, finite coproducts, quotients by finite groups, and the
mono/direct-summand axiom.  This structure is definitionally just the class
fields; it is used here to make each obligation a separately named projection. -/
structure S1736PreGaloisFields (C : Type u) [Category.{v} C] : Prop where
  /-- G1: finite limits (terminal object and pullbacks). -/
  finiteLimits : HasFiniteLimits C
  /-- G2: finite coproducts. -/
  finiteCoproducts : HasFiniteCoproducts C
  /-- G2: quotients by finite groups in the hom universe. -/
  finiteGroupQuotients : (G : Type v) → [Group G] → [Finite G] →
    HasColimitsOfShape (SingleObj G) C
  /-- G3: every mono is an isomorphism onto a direct summand. -/
  monoDirectSummand : ∀ {X Y : C} (i : X ⟶ Y) [Mono i],
    ∃ (Z : C) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))

/-- The field decomposition is exact: PreGaloisCategory C is equivalent to
the four obligations above.  In particular HasFiniteLimits is equivalent to
Mathlib's chosen HasTerminal + HasPullbacks pair. -/
theorem S1736PreGaloisCategory_iff_fields (C : Type u) [Category.{v} C] :
    PreGaloisCategory C ↔ S1736PreGaloisFields (C := C) := by
  constructor
  · intro h
    haveI : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
    exact
      { finiteLimits := inferInstance
        finiteCoproducts := h.hasFiniteCoproducts
        finiteGroupQuotients := fun G _ _ => h.hasQuotientsByFiniteGroups G
        monoDirectSummand := fun i _ => h.monoInducesIsoOnDirectSummand i }
  · intro h
    haveI : HasFiniteLimits C := h.finiteLimits
    exact
      { hasTerminal := inferInstance
        hasPullbacks := inferInstance
        hasFiniteCoproducts := h.finiteCoproducts
        hasQuotientsByFiniteGroups := fun G _ _ => h.finiteGroupQuotients G
        monoInducesIsoOnDirectSummand := fun i _ => h.monoDirectSummand i }

/-! ## 2. The actual S1728 category and its exact obligations -/

variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}

/-- The actual S1728 category on the represented finite-etale cover type.
Objects live in Type (u+1) and homs in Type (u+1). -/
abbrev S1736ActualCategory :
    Category.{u + 1, u + 1} (OrbicurveFiniteEtaleCover X) :=
  S1728CoverCategory11 (F := F) (X := X)

/-- The literal PreGaloisCategory obligation on the actual S1728 category.
No inhabitant is asserted. -/
def S1736ActualPreGaloisObligation : Prop :=
  @PreGaloisCategory.{u + 1, u + 1}
    (OrbicurveFiniteEtaleCover X) (S1736ActualCategory (F := F) (X := X))

/-- The same obligation decomposed into the four field groups. -/
def S1736ActualFieldObligation : Prop :=
  @S1736PreGaloisFields (OrbicurveFiniteEtaleCover X)
    (S1736ActualCategory (F := F) (X := X))

/-- The field decomposition applies to the actual S1728 category. -/
theorem S1736ActualPreGalois_iff_fields :
    S1736ActualPreGaloisObligation (F := F) (X := X) ↔
      S1736ActualFieldObligation (F := F) (X := X) :=
  @S1736PreGaloisCategory_iff_fields (OrbicurveFiniteEtaleCover X)
    (S1736ActualCategory (F := F) (X := X))

/-- The exact finite-limit obligation on the actual category (G1). -/
def S1736ObligationFiniteLimits : Prop :=
  @HasFiniteLimits (OrbicurveFiniteEtaleCover X)
    (S1736ActualCategory (F := F) (X := X))

/-- The exact finite-coproduct obligation on the actual category (G2). -/
def S1736ObligationFiniteCoproducts : Prop :=
  @HasFiniteCoproducts (OrbicurveFiniteEtaleCover X)
    (S1736ActualCategory (F := F) (X := X))

/-- The exact quotient-by-finite-groups obligation on the actual category
(G2), at the hom universe u+1. -/
def S1736ObligationFiniteGroupQuotients : Prop :=
  (G : Type (u + 1)) → [Group G] → [Finite G] →
    @HasColimitsOfShape (SingleObj G) _ (OrbicurveFiniteEtaleCover X)
      (S1736ActualCategory (F := F) (X := X))

/-- The exact mono/direct-summand obligation on the actual category (G3). -/
def S1736ObligationMonoDirectSummand : Prop :=
  ∀ {A B : OrbicurveFiniteEtaleCover X}
    (i : @Quiver.Hom _ (S1736ActualCategory (F := F) (X := X)).toQuiver A B) [Mono i],
    ∃ (Z : OrbicurveFiniteEtaleCover X)
      (u : @Quiver.Hom _ (S1736ActualCategory (F := F) (X := X)).toQuiver Z B),
      Nonempty (IsColimit (BinaryCofan.mk i u))

/-- The field obligation is exactly the conjunction of the four named
obligations. -/
theorem S1736ActualFieldObligation_iff :
    S1736ActualFieldObligation (F := F) (X := X) ↔
      S1736ObligationFiniteLimits (F := F) (X := X) ∧
      S1736ObligationFiniteCoproducts (F := F) (X := X) ∧
      S1736ObligationFiniteGroupQuotients (F := F) (X := X) ∧
      S1736ObligationMonoDirectSummand (F := F) (X := X) := by
  constructor
  · intro h
    exact ⟨h.finiteLimits, h.finiteCoproducts, h.finiteGroupQuotients,
      h.monoDirectSummand⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact
      { finiteLimits := h1
        finiteCoproducts := h2
        finiteGroupQuotients := h3
        monoDirectSummand := h4 }

/-! ## 3. The terminal field: exact missing input and conditional construction

The terminal object of the finite-etale cover category should be the identity
cover (X.stack, id_{X.stack}, finiteEtale).  The only missing datum for this
candidate is the finite-etale proof for the identity map.  Once supplied, the
terminal universal property is proved below in the actual S1728 category.
-/

/-- The exact missing geometric input for the terminal field: the identity
cover is representably finite etale. -/
def S1736IdentityFiniteEtale : Prop :=
  Nonempty (EtaleStackFiniteEtaleMorphism
    (Pseudofunctor.StrongTrans.id X.stack.fiber))

/-- The identity-cover candidate, given the missing finite-etale proof. -/
def S1736TerminalCover
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber)) :
    OrbicurveFiniteEtaleCover X where
  source := X.stack
  map := Pseudofunctor.StrongTrans.id X.stack.fiber
  finiteEtale := h

/-- The canonical candidate morphism from any cover to the identity cover. -/
noncomputable def S1736TerminalCoverMap
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber))
    (A : OrbicurveFiniteEtaleCover X) :
    OrbicurveFiniteEtaleCoverMap A (S1736TerminalCover (X := X) h) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  exact
    { map := A.map
      commutes := @Bicategory.rightUnitor Bicat _
        A.source.fiber X.stack.fiber A.map }

/-- Its class in the S1728 2-isomorphism quotient. -/
noncomputable def S1736TerminalMorphism
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber))
    (A : OrbicurveFiniteEtaleCover X) :
    @Quiver.Hom _ (S1736ActualCategory (F := F) (X := X)).toQuiver A
      (S1736TerminalCover (X := X) h) :=
  Quot.mk _ (S1736TerminalCoverMap (F := F) (X := X) h A)

/-- Uniqueness of the canonical morphism in the 2-isomorphism quotient. -/
theorem S1736TerminalMorphism_unique
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber))
    (A : OrbicurveFiniteEtaleCover X)
    (f : @Quiver.Hom _ (S1736ActualCategory (F := F) (X := X)).toQuiver A
      (S1736TerminalCover (X := X) h)) :
    f = S1736TerminalMorphism (F := F) (X := X) h A := by
  induction f using Quot.inductionOn with
  | h f =>
      change Quot.mk _ f = Quot.mk _
        (S1736TerminalCoverMap (F := F) (X := X) h A)
      apply Quot.sound
      exact ⟨(S1728RightUnitorIso f).symm ≪≫ f.commutes⟩

/-- The identity cover is terminal in the actual S1728 category, conditional
on the missing finite-etale proof. -/
def S1736TerminalCover_isTerminal
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber)) :
    @IsTerminal _ (S1736ActualCategory (F := F) (X := X))
      (S1736TerminalCover (X := X) h) :=
  IsTerminal.ofUniqueHom
    (fun A => S1736TerminalMorphism (F := F) (X := X) h A)
    (fun A f => S1736TerminalMorphism_unique (F := F) (X := X) h A f)

/-- The exact conditional construction of the terminal field. -/
theorem S1736HasTerminal_of_identity_finiteEtale
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber)) :
    @HasTerminal _ (S1736ActualCategory (F := F) (X := X)) :=
  (S1736TerminalCover_isTerminal (F := F) (X := X) h).hasTerminal

/-- If the identity cover is finite etale, then the actual S1728 category has
terminal objects.  Equivalently: the terminal field is reduced to
S1736IdentityFiniteEtale. -/
theorem S1736HasTerminal_of_identityFiniteEtale_prop
    (h : S1736IdentityFiniteEtale (F := F) (X := X)) :
    @HasTerminal _ (S1736ActualCategory (F := F) (X := X)) := by
  rcases h with ⟨h⟩
  exact S1736HasTerminal_of_identity_finiteEtale (F := F) (X := X) h

/-! ## 4. The remaining four PreGalois fields and the fiber functor:
exact missing obligations

No construction of the following is present in the tree.  Each proposition is
the literal class field at the actual S1728 category, so it is the complete
obligation; the comments record the geometric construction which would have to
be supplied.
-/

/-- G1 pullbacks: for two finite-etale covers A -> X and B -> X, one needs the
bicategorical fibre product of their underlying stacks, the finite-etale proof
for the two projections, and the universal property in the 2-isomorphism
quotient.  Mathlib has the definition
EtalePseudofunctorSquare.TwoPullbackWitness, but no construction of the
required square for covers.  This proposition is exactly the missing field. -/
def S1736PullbackObligation : Prop :=
  @HasPullbacks (OrbicurveFiniteEtaleCover X)
    (S1736ActualCategory (F := F) (X := X))

/-- G2 finite coproducts: the coproduct of two finite-etale covers is the
disjoint union of the underlying stacks over X, together with finite etaleness
of the two inclusions and the coproduct universal property after quotienting
by 2-isomorphism.  Neither the stack coproduct nor the finite-etale stability
is constructed in the tree. -/
def S1736FiniteCoproductObligation : Prop :=
  @HasFiniteCoproducts (OrbicurveFiniteEtaleCover X)
    (S1736ActualCategory (F := F) (X := X))

/-- G2 quotients by finite groups: for a finite group G acting on a cover A,
the quotient stack A/G with its finite-etale map to X and the colimit
universal property.  The tree contains the definition of a sign-action quotient
witness (OrbicurveSignQuotientWitness) but no construction of the quotient
stack or of its finite etaleness. -/
def S1736FiniteGroupQuotientObligation : Prop :=
  (G : Type (u + 1)) → [Group G] → [Finite G] →
    @HasColimitsOfShape (SingleObj G) _ (OrbicurveFiniteEtaleCover X)
      (S1736ActualCategory (F := F) (X := X))

/-- G3 mono/direct summand: every mono i : A -> B in the actual
2-isomorphism-quotient category must be a coproduct inclusion with an explicit
complement.  This is not derivable from terminal/pullback/coproduct data
alone (it is an axiom of the Mathlib class) and is not constructed. -/
def S1736MonoDirectSummandObligation : Prop :=
  ∀ {A B : OrbicurveFiniteEtaleCover X}
    (i : @Quiver.Hom _ (S1736ActualCategory (F := F) (X := X)).toQuiver A B) [Mono i],
    ∃ (Z : OrbicurveFiniteEtaleCover X)
      (u : @Quiver.Hom _ (S1736ActualCategory (F := F) (X := X)).toQuiver Z B),
      Nonempty (IsColimit (BinaryCofan.mk i u))

/-- The remaining fiber-functor obligation for the actual Category.{1,1}
object.  A fiber functor must land in FintypeCat.{u+1} and satisfy all six
FiberFunctor fields.  The geometric candidate is the base-changed fibre over
a chosen geometric point, but the tree only defines the fibre category
OrbicurveFiniteEtaleCover.GeometricFiber; it does not prove that this category
is a finite type, nor construct the functor or its identifications. -/
def S1736ActualFiberFunctorObligation
    (P : @PreGaloisCategory.{u + 1, u + 1}
      (OrbicurveFiniteEtaleCover X) (S1736ActualCategory (F := F) (X := X))) : Prop :=
  ∃ Fib : OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u + 1},
    Nonempty (@PreGaloisCategory.FiberFunctor
      (OrbicurveFiniteEtaleCover X) (S1736ActualCategory (F := F) (X := X)) P Fib)

/-- The literal GaloisCategory obligation on the actual Category.{1,1}.
No inhabitant is asserted. -/
def S1736ActualGaloisObligation : Prop :=
  @GaloisCategory.{u + 1, u + 1}
    (OrbicurveFiniteEtaleCover X) (S1736ActualCategory (F := F) (X := X))

/-- From a PreGalois structure and a fiber functor on the actual Category.{1,1},
the actual GaloisCategory follows.  This is a genuine conditional assembly; it
does not construct either input. -/
theorem S1736ActualGaloisCategoryOfInputs
    (P : @PreGaloisCategory.{u + 1, u + 1}
      (OrbicurveFiniteEtaleCover X) (S1736ActualCategory (F := F) (X := X)))
    (hF : S1736ActualFiberFunctorObligation (F := F) (X := X) P) :
    S1736ActualGaloisObligation (F := F) (X := X) := by
  rcases hF with ⟨Fib, ⟨hFib⟩⟩
  exact
    { toPreGaloisCategory := P
      hasFiberFunctor := ⟨Fib, ⟨hFib⟩⟩ }

/-! ### 3.1. Assembling the actual PreGalois instance from the five inputs

The following theorem is the exact sufficiency statement for the obligation
list: if the five fields are supplied (the terminal field by the identity
finite-etale proof, the other four as the named propositions of Section 4),
then the actual Category.{1,1} is a PreGaloisCategory.  It constructs nothing
new geometrically; it only assembles the class. -/

/-- Assembling the actual PreGaloisCategory from the five exact inputs. -/
theorem S1736PreGaloisCategoryOfInputs
    (hTerm : S1736IdentityFiniteEtale (F := F) (X := X))
    (hPull : S1736PullbackObligation (F := F) (X := X))
    (hCoprod : S1736FiniteCoproductObligation (F := F) (X := X))
    (hQuot : S1736FiniteGroupQuotientObligation (F := F) (X := X))
    (hMono : S1736MonoDirectSummandObligation (F := F) (X := X)) :
    S1736ActualPreGaloisObligation (F := F) (X := X) :=
  { hasTerminal := S1736HasTerminal_of_identityFiniteEtale_prop hTerm
    hasPullbacks := hPull
    hasFiniteCoproducts := hCoprod
    hasQuotientsByFiniteGroups := fun G _ _ => hQuot G
    monoInducesIsoOnDirectSummand := fun i _ => hMono i }

/-- The finite-limit field reduces exactly to the identity finite-etale proof
plus the pullback field. -/
theorem S1736HasFiniteLimits_of_inputs
    (hTerm : S1736IdentityFiniteEtale (F := F) (X := X))
    (hPull : S1736PullbackObligation (F := F) (X := X)) :
    S1736ObligationFiniteLimits (F := F) (X := X) := by
  letI : @HasTerminal _ (S1736ActualCategory (F := F) (X := X)) :=
    S1736HasTerminal_of_identityFiniteEtale_prop hTerm
  letI : @HasPullbacks _ (S1736ActualCategory (F := F) (X := X)) := hPull
  exact hasFiniteLimits_of_hasTerminal_and_pullbacks

/-! ## 5. The literal target universe Category.{0,1}

For F : Type (the S1726 orbicurve) the stored coverCategory is
Category.{0,1} (OrbicurveFiniteEtaleCover X): objects Type 1, homs Type 0.
The actual cover-map type is Type 1, so this requires S1728's explicit small
carrier family.  The following section constructs the target GaloisCategory
conditionally on that family and on the PreGalois/fiber-functor inputs.
-/

namespace S1736TargetUniverse

open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

/-- The S1726 D6 orbicurve cover type, at the literal target universe. -/
abbrev S1736TargetCover : Type 1 := S1728Cover

/-- The actual cover-map type of the target cover type. -/
abbrev S1736TargetCoverMap (A B : S1736TargetCover) : Type 1 :=
  S1728CoverMap A B

/-- The literal target field type: Category.{0,1}. -/
def S1736TargetCoverCategory : Type 1 :=
  Category.{0, 1} S1736TargetCover

/-- The universe-corrected field type: Category.{1,1}, matching the actual
cover-map type. -/
def S1736CorrectedCoverCategory : Type 2 :=
  Category.{1, 1} S1736TargetCover

/-- Exact small-Hom condition: a Type-0 carrier for each actual cover-map type.
This is the additional input which S1728 showed is necessary for the literal
Category.{0,1} field. -/
def S1736TargetSmallCoverDataObligation : Prop :=
  S1728SmallRawCoverDataRequired

/-- The literal target Galois-category field type for a chosen cover category. -/
def S1736TargetGaloisCategory
    (C : S1736TargetCoverCategory) : Prop :=
  @GaloisCategory.{1, 0} S1736TargetCover C

/-- The target requires Type-0 homs. -/
example (C : S1736TargetCoverCategory) (A B : S1736TargetCover) : Type :=
  @Quiver.Hom _ C.toQuiver A B

/-- The actual cover-map type is Type 1, so it cannot literally be the hom
type of the target Category.{0,1}. -/
example (A B : S1736TargetCover) : Type 1 :=
  S1736TargetCoverMap A B

/-- The two target fields analysed by this file. -/
structure S1736TargetCoverAndGalois where
  coverCategory : S1736TargetCoverCategory
  galoisCategory :
    @GaloisCategory.{1, 0} S1736TargetCover coverCategory

section TargetInputs

variable [C : Category.{0, 1} S1736TargetCover]

/-- The remaining PreGalois obligation at the target universe. -/
def S1736TargetPreGaloisObligation : Prop :=
  @PreGaloisCategory.{1, 0} S1736TargetCover C

/-- The fiber-functor obligation at the target universe, relative to a
PreGalois structure. -/
def S1736TargetFiberFunctorObligation
    (P : S1736TargetPreGaloisObligation (C := C)) : Prop :=
  ∃ F : S1736TargetCover ⥤ FintypeCat.{0},
    Nonempty (@PreGaloisCategory.FiberFunctor
      S1736TargetCover C P F)

/-- Conditional construction of the target GaloisCategory from the two exact
remaining inputs: PreGaloisCategory at Category.{0,1} and a fiber functor to
FintypeCat.{0}.  No field is asserted unconditionally. -/
theorem S1736TargetGaloisCategoryOfInputs
    (P : S1736TargetPreGaloisObligation (C := C))
    (hF : S1736TargetFiberFunctorObligation (C := C) P) :
    @GaloisCategory.{1, 0} S1736TargetCover C := by
  rcases hF with ⟨F, ⟨hF⟩⟩
  exact
    { toPreGaloisCategory := P
      hasFiberFunctor := ⟨F, ⟨hF⟩⟩ }

end TargetInputs

/-- From the small-Hom family and the two target-universe inputs, the literal
target pair (coverCategory, galoisCategory) is constructed.  This is the
conditional answer to the task: Category.{0,1} is the hard prerequisite, and
GaloisCategory is built from the PreGalois structure plus a fiber functor. -/
def S1736TargetPackageOfInputs
    (H : (A B : S1736TargetCover) → Type)
    (e : ∀ A B, H A B ≃ S1736TargetCoverMap A B)
    (P : @PreGaloisCategory.{1, 0} S1736TargetCover
      (S1728ActualCategory01 H e))
    (hF : S1736TargetFiberFunctorObligation
      (C := S1728ActualCategory01 H e) P) :
    S1736TargetCoverAndGalois where
  coverCategory := S1728ActualCategory01 H e
  galoisCategory :=
    S1736TargetGaloisCategoryOfInputs
      (C := S1728ActualCategory01 H e) P hF

/-- The literal target fields projected from the conditional package. -/
theorem S1736TargetPackageOfInputs_coverCategory
    (H : (A B : S1736TargetCover) → Type)
    (e : ∀ A B, H A B ≃ S1736TargetCoverMap A B)
    (P : @PreGaloisCategory.{1, 0} S1736TargetCover
      (S1728ActualCategory01 H e))
    (hF : S1736TargetFiberFunctorObligation
      (C := S1728ActualCategory01 H e) P) :
    (S1736TargetPackageOfInputs H e P hF).coverCategory =
      S1728ActualCategory01 H e := rfl

/-- Any full OrbicurveEtaleFundamentalGroup restricts to the two fields. -/
noncomputable def S1736TargetPackageOfEtalePi
    {G : ProfiniteGrp.{0}}
    (D : Iut.OrbicurveEtaleFundamentalGroup (F := S1726K) S1726Orbicurve G) :
    S1736TargetCoverAndGalois where
  coverCategory := D.coverCategory
  galoisCategory := D.galoisCategory

end S1736TargetUniverse

open S1736TargetUniverse

/-!
## 6. Status summary

Constructed unconditionally:
* the actual Category.{1,1} on OrbicurveFiniteEtaleCover X (S1728 import);
* the exact field decomposition PreGaloisCategory C <-> S1736PreGaloisFields C;
* the equivalence between the field bundle and the four named obligations.

Constructed conditionally:
* HasTerminal from the identity finite-etale proof;
* HasFiniteLimits from the identity finite-etale proof plus pullbacks;
* PreGaloisCategory from the five exact inputs;
* GaloisCategory from PreGaloisCategory plus a fiber functor;
* the literal target pair (coverCategory, galoisCategory) from the S1728
  small-Hom family plus the target-universe PreGalois and fiber-functor inputs.

Missing (exact propositions, no inhabitants):
* S1736IdentityFiniteEtale (terminal field);
* S1736PullbackObligation, S1736FiniteCoproductObligation,
  S1736FiniteGroupQuotientObligation, S1736MonoDirectSummandObligation;
* S1736ActualFiberFunctorObligation;
* S1736TargetSmallCoverDataObligation (S1728 small-Hom family);
* the target-universe PreGalois and fiber-functor inputs.

No sorry, no axiom, no fake instance.
-/

/-! ## 7. Axiom audit and final markers -/

#print axioms S1736PreGaloisCategory_iff_fields
#print axioms S1736ActualFieldObligation_iff
#print axioms S1736TerminalCover_isTerminal
#print axioms S1736HasTerminal_of_identity_finiteEtale
#print axioms S1736ActualGaloisCategoryOfInputs
#print axioms S1736PreGaloisCategoryOfInputs
#print axioms S1736HasFiniteLimits_of_inputs
#print axioms S1736TargetGaloisCategoryOfInputs
#print axioms S1736TargetPackageOfInputs

#check S1736PreGaloisCategory_iff_fields
#check S1736ActualPreGaloisObligation
#check S1736ActualFieldObligation
#check S1736ObligationFiniteLimits
#check S1736ObligationFiniteCoproducts
#check S1736ObligationFiniteGroupQuotients
#check S1736ObligationMonoDirectSummand
#check S1736IdentityFiniteEtale
#check S1736HasTerminal_of_identity_finiteEtale
#check S1736PreGaloisCategoryOfInputs
#check S1736HasFiniteLimits_of_inputs
#check S1736PullbackObligation
#check S1736FiniteCoproductObligation
#check S1736FiniteGroupQuotientObligation
#check S1736MonoDirectSummandObligation
#check S1736ActualFiberFunctorObligation
#check S1736ActualGaloisObligation
#check S1736TargetCoverCategory
#check S1736CorrectedCoverCategory
#check S1736TargetSmallCoverDataObligation
#check S1736TargetPreGaloisObligation
#check S1736TargetFiberFunctorObligation
#check S1736TargetGaloisCategoryOfInputs
#check S1736TargetPackageOfInputs
#check S1736TargetPackageOfEtalePi

end LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual