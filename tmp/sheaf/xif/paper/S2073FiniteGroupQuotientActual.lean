import tmp.sheaf.xif.paper.S2071CurveCardGaloisActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import LeanFormal.IUT.Foundations.Geometry.ClopenFiniteComplement
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineBaseFiniteEtaleQuotients
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPointsGeneral
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

/-!
# S2073: the first missing hasQuotientsByFiniteGroups (finite-group quotients of
finite etale covers)

Target: for X : Scheme, G finite, and a finite etale cover Y of X with a
G-action over X, construct the canonical quotient Y/G as a finite etale
cover of X, and derive
Limits.HasColimitsOfShape (SingleObj G) (FiniteEtaleCover X).

## Result of the attempt

The construction does **not** follow from Mathlib 4.32.2.  Searched over
Mathlib.AlgebraicGeometry and Mathlib.CategoryTheory:

* no scheme quotient by a finite group action (no Scheme.Quotient, no GIT, no
  invariant subscheme construction, no quotient by a finite flat equivalence
  relation, i.e. no SGA3 V.4);
* no relative Spec of a quasi-coherent sheaf of algebras (Spec_X A), hence no
  sheaf-of-invariants construction A^G on a general base;
* no equivalence between finite locally constant etale sheaves and finite etale
  schemes, so the Galois-category route (SGA1 V.4) is unavailable;
* PreGaloisCategory.hasQuotientsByFiniteGroups is an *axiom field* of the class
  (Mathlib.CategoryTheory.Galois.Basic), not a theorem, so it cannot be
  instantiated for FiniteEtaleCover X without this very construction.

What Mathlib *does* provide and that is used below: Etale and IsFinite are
stable under composition and base change and descend along fpqc/fppf morphisms
(Mathlib.AlgebraicGeometry.Morphisms.Etale,
...Morphisms.Finite, ...Morphisms.FlatDescent, ...Morphisms.Descent); the
section ring of a finite etale cover of an affine base is finite etale over the
base.

What this project already provides (imported below, not reproved):

* FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale: for a finite
  etale R-algebra A with an action of a finite group, A^G is finite etale
  over R (no invertibility of |G|, no Noetherian and no local hypothesis);
* AffineGeneralQuotientG2Consumer.affineQuotientCoverGeneral: the affine
  quotient cover Spec (A^G) -> Spec R as an actual FiniteEtaleCover;
* AffineBaseFiniteEtaleQuotients.actionCoconeOfDiagram: for
  F : SingleObj G ⥤ FiniteEtaleCover (Spec R), the quotient cocone with point
  the affine quotient cover and invariant projection quotientProjectionOfDiagram;
* AffineQuotientIntegration.affineQuotientUniversal: the affine-**target**
  universal property for invariant morphisms into Spec B;
* ClopenFiniteComplement.FiniteGroupQuotient.hasColimit_of_hasCoequalizer: if
  the coequalizer of the action pair (∐_g Y, ∐_g Y) ⇒ Y exists, the action
  diagram has a colimit.

The exact first missing statement is S2073AffineActionCoconeIsColimit below
(the affine-base colimit of actionCoconeOfDiagram, i.e. the transport of the
existing affine-target universal property to arbitrary finite etale targets),
together with S2073GlobalActionCoconeIsColimit for the passage from affine to
arbitrary base by Zariski gluing.  Neither is inhabited here, and neither is
replaced by a Nonempty gate: both are Type-valued structures carrying the
actual quotient datum and universal property.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.defProp false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S2073FiniteGroupQuotientActual

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
open ABCBridge.AffineBaseFiniteEtaleQuotients

universe u v

/-! ## 1. Categorical layer: a SingleObj G-colimit is a quotient -/

section Categorical

variable {C : Type u} [Category.{v, u} C]
variable {G : Type v} [Group G]

/-- The cocone attached to an invariant map out of the unique object.  A cocone
over rho : SingleObj G ⥤ C is determined by its component at the unique object;
the naturality square is exactly the invariance condition. -/
def S2073CoconeOf (ρ : SingleObj G ⥤ C) (Q : C)
    (q : ρ.obj (SingleObj.star G) ⟶ Q)
    (hq : ∀ g : G, ρ.map g ≫ q = q) : Cocone ρ :=
  Cocone.mk Q (SingleObj.natTrans (F := ρ)
    (G := (Functor.const (SingleObj G)).obj Q) q
    (by
      intro g
      erw [Functor.const_obj_map]
      show ρ.map g ≫ q = q ≫ 𝟙 Q
      rw [Category.comp_id]
      exact hq g))

/-- The component at the unique object of S2073CoconeOf. -/
@[simp]
theorem S2073CoconeOf_ι_star (ρ : SingleObj G ⥤ C) (Q : C)
    (q : ρ.obj (SingleObj.star G) ⟶ Q)
    (hq : ∀ g : G, ρ.map g ≫ q = q) :
    (S2073CoconeOf ρ Q q hq).ι.app (SingleObj.star G) = q := rfl

/-- Quotient data for a finite-group action diagram: the quotient object, the
invariant projection, and the universal property restricted to invariant maps out
of the acted object.  This is Type-valued data; no Nonempty gate and no
inhabitant is asserted. -/
structure S2073QuotientData (ρ : SingleObj G ⥤ C) : Type (max u v) where
  /-- the quotient object -/
  Q : C
  /-- the quotient projection -/
  q : ρ.obj (SingleObj.star G) ⟶ Q
  /-- the projection is invariant under the action -/
  invariant : ∀ g : G, ρ.map g ≫ q = q
  /-- the universal property: every invariant map out of the acted object factors
  through the quotient -/
  desc : ∀ (T : C) (f : ρ.obj (SingleObj.star G) ⟶ T),
    (∀ g : G, ρ.map g ≫ f = f) → (Q ⟶ T)
  /-- the factorization equation -/
  fac : ∀ (T : C) (f : ρ.obj (SingleObj.star G) ⟶ T)
    (hf : ∀ g : G, ρ.map g ≫ f = f), q ≫ desc T f hf = f
  /-- uniqueness of the factorization -/
  uniq : ∀ (T : C) (f : ρ.obj (SingleObj.star G) ⟶ T)
    (hf : ∀ g : G, ρ.map g ≫ f = f) (m : Q ⟶ T), q ≫ m = f → m = desc T f hf

namespace S2073QuotientData

variable {ρ : SingleObj G ⥤ C}

/-- The cocone carried by quotient data. -/
def cocone (D : S2073QuotientData ρ) : Cocone ρ :=
  S2073CoconeOf ρ D.Q D.q D.invariant

/-- Quotient data is a colimit cocone: this is the categorical content of the
universal property in the cover category. -/
def isColimit (D : S2073QuotientData ρ) : IsColimit D.cocone where
  desc s := D.desc s.pt (s.ι.app (SingleObj.star G))
    (fun g => Cocone.w s (j := SingleObj.star G) (j' := SingleObj.star G) g)
  fac s j := by
    have hj : j = SingleObj.star G := Subsingleton.elim j _
    subst hj
    exact D.fac s.pt (s.ι.app (SingleObj.star G))
      (fun g => Cocone.w s (j := SingleObj.star G) (j' := SingleObj.star G) g)
  uniq s m hm :=
    D.uniq s.pt (s.ι.app (SingleObj.star G))
      (fun g => Cocone.w s (j := SingleObj.star G) (j' := SingleObj.star G) g) m
      (hm (SingleObj.star G))

/-- Quotient data yields the colimit. -/
theorem hasColimit (D : S2073QuotientData ρ) : HasColimit ρ :=
  HasColimit.mk ⟨D.cocone, D.isColimit⟩

end S2073QuotientData

/-- Conversely, an actual colimit of an action diagram is quotient data. -/
def S2073quotientDataOfHasColimit (ρ : SingleObj G ⥤ C) [HasColimit ρ] :
    S2073QuotientData ρ where
  Q := colimit ρ
  q := colimit.ι ρ (SingleObj.star G)
  invariant g := colimit.w ρ g
  desc T f hf := colimit.desc ρ (S2073CoconeOf ρ T f hf)
  fac T f hf := colimit.ι_desc (S2073CoconeOf ρ T f hf) (SingleObj.star G)
  uniq T f hf m hm := by
    refine (colimit.isColimit ρ).uniq (S2073CoconeOf ρ T f hf) m ?_
    intro j
    have hj : j = SingleObj.star G := Subsingleton.elim j _
    subst hj
    exact hm

/-- The card field follows from an explicit quotient construction for every
action diagram. -/
theorem S2073hasColimitsOfShape_of_quotientData (G : Type v) [Group G] [Finite G]
    (h : ∀ ρ : SingleObj G ⥤ C, S2073QuotientData ρ) :
    HasColimitsOfShape (SingleObj G) C :=
  ⟨fun ρ => (h ρ).hasColimit⟩

/-- Conversely the card field produces quotient data: the target is *exactly*
the existence of the quotient objects together with their universal property, not
the categorical packaging. -/
def S2073quotientData_of_hasColimitsOfShape (G : Type v) [Group G] [Finite G]
    (h : HasColimitsOfShape (SingleObj G) C) :
    ∀ ρ : SingleObj G ⥤ C, S2073QuotientData ρ := by
  intro ρ
  haveI : HasColimit ρ := h.has_colimit ρ
  exact S2073quotientDataOfHasColimit ρ

/-- A Type-valued provider of quotients for every finite group and every action
diagram.  This is the exact content of the card, unpacked. -/
def S2073QuotientDataProvider (C : Type u) [Category.{v, u} C] : Type (max u (v + 1)) :=
  ∀ (G : Type v) [Group G] [Finite G], ∀ ρ : SingleObj G ⥤ C, S2073QuotientData ρ

/-- The provider gives the card field. -/
theorem S2073hasColimitsOfShape_of_provider (h : S2073QuotientDataProvider C) :
    ∀ (G : Type v) [Group G] [Finite G], HasColimitsOfShape (SingleObj G) C :=
  fun G _ _ => S2073hasColimitsOfShape_of_quotientData G (h G)

end Categorical

/-! ## 2. The cover category of a scheme and the curve card -/

section Covers

variable (S : Scheme.{u})

/-- The exact hasQuotientsByFiniteGroups field of
CurvePreGaloisCategoryRemainingFields S. -/
def S2073HasQuotientsByFiniteGroups (S : Scheme.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S)

/-- The cover-category form of the quotient-data provider. -/
def S2073CoverQuotientDataProvider (S : Scheme.{u}) : Type (u + 1) :=
  ∀ (G : Type u) [Group G] [Finite G]
    (ρ : SingleObj G ⥤ FiniteEtaleCover S), S2073QuotientData ρ

/-- Unpacking the card field into actual quotient data. -/
def S2073coverQuotientData_of_hasQuotients
    (h : S2073HasQuotientsByFiniteGroups S) :
    S2073CoverQuotientDataProvider S :=
  fun G _ _ ρ => S2073quotientData_of_hasColimitsOfShape G (h G) ρ

/-- The card field from actual quotient data. -/
theorem S2073hasQuotients_of_coverQuotientData
    (h : S2073CoverQuotientDataProvider S) :
    S2073HasQuotientsByFiniteGroups S :=
  fun G _ _ => S2073hasColimitsOfShape_of_quotientData G (h G)

/-- The card field implies the frozen remaining-fields card of the curve
Galois-category file. -/
theorem S2073remainingFields_of_hasQuotients
    (h : S2073HasQuotientsByFiniteGroups S) :
    CurvePreGaloisCategoryRemainingFields S :=
  ⟨h⟩

/-- Conversely the frozen card gives the card field. -/
theorem S2073hasQuotients_of_remainingFields
    (h : CurvePreGaloisCategoryRemainingFields S) :
    S2073HasQuotientsByFiniteGroups S :=
  h.hasQuotientsByFiniteGroups

end Covers

/-! ## 3. What is actually provable: the affine quotient cover is finite etale

The hard analytic input (A^G finite etale over R) is
FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale, already proved in
this project.  The two lemmas below record that the resulting affine quotient
cover really is a finite etale cover, i.e. that Etale and IsFinite are
preserved. -/

section AffineQuotient

variable {R : Type u} [CommRing R]

/-- The affine fixed-point quotient cover has etale structure morphism. -/
theorem S2073affineQuotientCover_etale
    (A : Type u) [CommRing A] [Algebra R A]
    (G : Type u) [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] :
    Etale (affineQuotientCoverGeneral (R := R) A G).structureMap :=
  (affineQuotientCoverGeneral (R := R) A G).etale_structureMap

/-- The affine fixed-point quotient cover has finite structure morphism. -/
theorem S2073affineQuotientCover_finite
    (A : Type u) [CommRing A] [Algebra R A]
    (G : Type u) [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A] :
    IsFinite (affineQuotientCoverGeneral (R := R) A G).structureMap :=
  (affineQuotientCoverGeneral (R := R) A G).finite_structureMap

/-- The affine-target universal property in cover form: an invariant R-algebra
map B -> A produces a morphism out of the affine quotient cover, and it
factors the induced cover morphism. -/
theorem S2073affineQuotientCover_lift
    (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (G : Type u) [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.Etale R A] [Module.Finite R A]
    (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    ∃ u : affineQuotientCoverGeneral (R := R) A G ⟶
        affineCover (R := R) B hEtB hFinB,
      affineQuotientCoverMapGeneral (R := R) A G ≫ u =
        affineCoverMapOfAlgHom (R := R) (A := A) (B := B)
          inferInstance inferInstance hEtB hFinB φ :=
  affineQuotientCover_liftGeneral
    (R := R) (A := A) (B := B) (G := G) hEtB hFinB φ hφ

end AffineQuotient

/-! ## 4. The exact first missing statements -/

/-- **S2073-M1 (affine base).**  For every commutative ring R and every finite
group action diagram F : SingleObj G ⥤ FiniteEtaleCover (Spec R), the quotient
cocone built from the affine fixed-point quotient cover
(AffineBaseFiniteEtaleQuotients.actionCoconeOfDiagram) is a colimit.

This is the exact statement that is missing: the existing affine universal
property (AffineQuotientIntegration.affineQuotientUniversal) is stated for
affine *targets* Spec B, while a colimit in FiniteEtaleCover (Spec R) requires
the factorization for every finite etale cover target T (transport along
T.carrier.isoSpec).  Neither Mathlib nor this project currently supplies that
transport, and no inhabitant of this structure is constructed here. -/
structure S2073AffineActionCoconeIsColimit (R : Type u) [CommRing R] : Type (u + 1) where
  /-- the affine quotient cocone of every finite-group action diagram is a colimit -/
  isColimit : ∀ (G : Type u) [Group G] [Finite G]
    (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R))),
    IsColimit (actionCoconeOfDiagram (R := R) (G := G) F).cocone

/-- **S2073-M1 implies the card field over an affine base.** -/
theorem S2073affineHasQuotients_of_coconeIsColimit {R : Type u} [CommRing R]
    (h : S2073AffineActionCoconeIsColimit R) :
    S2073HasQuotientsByFiniteGroups (Spec (CommRingCat.of R)) := by
  intro G _ _
  refine ⟨fun F => ?_⟩
  exact HasColimit.mk ⟨_, h.isColimit G F⟩

/-- **S2073-M2 (affine to arbitrary base).**  Every finite-group action diagram in
the finite etale cover category of an arbitrary scheme has a quotient cocone
which is a colimit.  This is the Zariski-gluing step (choose a G-invariant
affine open cover, take affine quotients, glue along invariant intersections,
and check finite etale descent); the project's AffineLocalQuotientPreglueData /
GlobalGluedQuotientData interface is the existing partial infrastructure. -/
structure S2073GlobalActionCoconeIsColimit (S : Scheme.{u}) : Type (u + 1) where
  /-- the quotient cocone data for every finite-group action diagram -/
  cocone : ∀ (G : Type u) [Group G] [Finite G]
    (F : SingleObj G ⥤ FiniteEtaleCover S), GlobalActionCoconeData S G F
  /-- each such cocone is a colimit -/
  isColimit : ∀ (G : Type u) [Group G] [Finite G]
    (F : SingleObj G ⥤ FiniteEtaleCover S), IsColimit (cocone G F).cocone

/-- **S2073-M2 implies the card field for every scheme.** -/
theorem S2073hasQuotients_of_globalCoconeIsColimit {S : Scheme.{u}}
    (h : S2073GlobalActionCoconeIsColimit S) :
    S2073HasQuotientsByFiniteGroups S := by
  intro G _ _
  refine ⟨fun F => ?_⟩
  exact HasColimit.mk ⟨(h.cocone G F).cocone, h.isColimit G F⟩

/-- The curve-card consumer: over an affine base the affine statement alone gives
the frozen remaining-fields card. -/
def S2073affineRemainingFields_of_coconeIsColimit {R : Type u} [CommRing R]
    (h : S2073AffineActionCoconeIsColimit R) :
    CurvePreGaloisCategoryRemainingFields (Spec (CommRingCat.of R)) :=
  S2073remainingFields_of_hasQuotients _
    (S2073affineHasQuotients_of_coconeIsColimit h)

/-! ## 5. The curve-card consumer -/

/-- The actual source curve is definitionally the spectrum of its coordinate ring,
so the affine-base statement is exactly what the curve card needs. -/
theorem S2073curveScheme_eq_spec_coordinateRing (K : Type u) [Field K] :
    curveScheme K = Spec (CommRingCat.of (curveCoordinateRing K)) :=
  rfl

/-- The curve's hasQuotientsByFiniteGroups from the affine-base statement at the
Weierstrass coordinate ring. -/
theorem S2073curveHasQuotients_of_affine {K : Type u} [Field K]
    (h : S2073AffineActionCoconeIsColimit (curveCoordinateRing K)) :
    S2073HasQuotientsByFiniteGroups (curveScheme K) := by
  rw [S2073curveScheme_eq_spec_coordinateRing K]
  exact S2073affineHasQuotients_of_coconeIsColimit h

/-- The frozen curve card's remaining field from the affine-base statement. -/
def S2073curveRemainingFields_of_affine {K : Type u} [Field K]
    (h : S2073AffineActionCoconeIsColimit (curveCoordinateRing K)) :
    CurvePreGaloisCategoryRemainingFields (curveScheme K) :=
  S2073curveHasQuotients_of_affine h |> S2073remainingFields_of_hasQuotients _

/-! ## 6. Axiom probes -/

#print axioms S2073CoconeOf
#print axioms S2073QuotientData.isColimit
#print axioms S2073quotientDataOfHasColimit
#print axioms S2073hasColimitsOfShape_of_quotientData
#print axioms S2073quotientData_of_hasColimitsOfShape
#print axioms S2073hasQuotients_of_coverQuotientData
#print axioms S2073remainingFields_of_hasQuotients
#print axioms S2073affineQuotientCover_etale
#print axioms S2073affineQuotientCover_finite
#print axioms S2073affineQuotientCover_lift
#print axioms S2073affineHasQuotients_of_coconeIsColimit
#print axioms S2073hasQuotients_of_globalCoconeIsColimit
#print axioms S2073curveHasQuotients_of_affine

end LeanFormal.IUT.XiFPaper.S2073FiniteGroupQuotientActual
end
