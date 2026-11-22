import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveEtaleCovers
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveConnectedness
import LeanFormal.IUT.IUTII.Frobenioid.Example36SpecCoverEquivalenceFinal
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# S1760: the function-field comparison for finite etale covers

This file constructs the actual comparison functor from finite etale covers of
an integral scheme X to finite etale algebras over the function field
K = X.functionField:

* S1760GenericPointMap : Spec K --> X is the canonical map from the spectrum of
  the function field (the generic point);
* S1760GenericFiberFunctor : FiniteEtaleCover X --> (FiniteEtale K)^op is the
  composite of base change along the generic point with the proved field-case
  Spec/Gamma equivalence (FiniteEtale K)^op ~= FiniteEtaleCover (Spec K).

The functor is constructed unconditionally.  The file then identifies exactly
what is missing for the asserted category equivalence:

* the general affine Spec/Gamma equivalence
  FiniteEtaleCover (Spec R) ~= (FiniteEtale R)^op for a non-field base R
  (only the field case is in the project/Mathlib);
* fullness of the generic-fibre functor, which on the algebra side reduces to
  the normal-base integral-descent lemma
  IsIntegrallyClosedIn B (B (x)_R K) for a finite etale R-algebra B;
* essential surjectivity.  As stated for all finite etale K-algebras this is
  mathematically FALSE: a finite separable extension of K ramified at a
  finite point of the punctured curve does not come from a finite etale cover.
  The correct target is the full subcategory of finite etale K-algebras
  unramified over the curve, whose construction requires normalisation of the
  curve in a finite extension; this is not available in Mathlib 4.32.2.

No equivalence is asserted, no sorry, no new axiom, no fake hypothesis.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1760FunctionFieldCoversActual

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverEquivalenceFinal
open scoped TensorProduct

universe u

/-! ## 1. The generic point and the generic-fibre comparison functor -/

section GenericFiber

variable (X : Scheme.{u}) [IsIntegral X]

/-- The function field of an integral scheme, as a field type. -/
abbrev S1760FunctionField : Type u := X.functionField

instance S1760FunctionField_field : Field (S1760FunctionField X) := inferInstance

/-- The canonical morphism Spec K --> X from the spectrum of the function
field (the generic point of X). -/
noncomputable def S1760GenericPointMap :
    Spec (CommRingCat.of (S1760FunctionField X)) ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/-- The generic fibre of a finite etale cover of X: base change along the
generic point. -/
noncomputable def S1760GenericFiber (C : FiniteEtaleCover X) :
    FiniteEtaleCover (Spec (CommRingCat.of (S1760FunctionField X))) :=
  (FiniteEtaleCover.pullback (S1760GenericPointMap X)).obj C

/-- The generic-fibre comparison functor: cover first to the generic point, then
use the actual field-case equivalence between finite etale covers of Spec K
and finite etale K-algebras. -/
noncomputable def S1760GenericFiberFunctor :
    FiniteEtaleCover X ⥤ (CommAlgCat.FiniteEtale.{u} (S1760FunctionField X))ᵒᵖ :=
  FiniteEtaleCover.pullback (S1760GenericPointMap X) ⋙
    (specCoverEquivalence (S1760FunctionField X)).inverse

@[simp]
theorem S1760GenericFiberFunctor_obj (C : FiniteEtaleCover X) :
    (S1760GenericFiberFunctor X).obj C =
      (specCoverEquivalence (S1760FunctionField X)).inverse.obj
        (S1760GenericFiber X C) := rfl

/-- The asserted category equivalence of the function-field comparison. -/
def S1760GenericFiberEquivalence : Prop :=
  (S1760GenericFiberFunctor X).IsEquivalence

/-- The fullness half of the asserted equivalence. -/
def S1760GenericFiberFull : Prop :=
  (S1760GenericFiberFunctor X).Full

/-- The essential-surjectivity half of the asserted equivalence. -/
def S1760GenericFiberEssSurj : Prop :=
  (S1760GenericFiberFunctor X).EssSurj

/-- The connected-cover half of the asserted correspondence: a connected
finite etale cover of an integral scheme should have field generic fibre.  This
is not proved here; it requires the standard theorem that connected components
of a finite flat cover are detected on the generic fibre. -/
def S1760ConnectedGenericFiberIsField : Prop :=
  ∀ (C : FiniteEtaleCover X), ConnectedSpace C.carrier →
    IsField ((S1760GenericFiberFunctor X).obj C).unop.obj

/-- The converse connectedness statement. -/
def S1760FieldGenericFiberConnected : Prop :=
  ∀ (C : FiniteEtaleCover X),
    IsField ((S1760GenericFiberFunctor X).obj C).unop.obj → ConnectedSpace C.carrier

/-- The asserted equivalence is exactly faithful + full + essentially
surjective.  The faithful part is not proved for a general X; this theorem
only records the exact decomposition. -/
theorem S1760GenericFiberEquivalence_iff :
    S1760GenericFiberEquivalence X ↔
      (S1760GenericFiberFunctor X).Faithful ∧
        S1760GenericFiberFull X ∧ S1760GenericFiberEssSurj X := by
  unfold S1760GenericFiberEquivalence S1760GenericFiberFull S1760GenericFiberEssSurj
  exact ⟨fun h => ⟨h.faithful, h.full, h.essSurj⟩,
    fun h => { faithful := h.1, full := h.2.1, essSurj := h.2.2 }⟩

end GenericFiber

/-! ## 2. The algebraic comparison at the level of coordinate rings -/

section Algebra

variable (R : Type u) [CommRing R] [IsDomain R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The algebraic base-change comparison: a finite etale R-algebra is sent to
its base change to the fraction field K. -/
abbrev S1760BaseChangeFunctor :
    (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ⥤ (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ :=
  (CommAlgCat.FiniteEtale.baseChange.{u, u, u} R K).op

/-- The base-change comparison is faithful: a map of finite etale R-algebras
is determined by its base change to the fraction field.  This is unconditional
and is the concrete algebraic form of the generic-fibre comparison. -/
theorem S1760BaseChange_faithful :
    (CommAlgCat.FiniteEtale.baseChange.{u, u, u} R K).Faithful := by
  refine ⟨?_⟩
  intro A B f g h
  ext a
  have h1 := congrArg (fun φ : (CommAlgCat.FiniteEtale.baseChange.{u, u, u} R K).obj A ⟶
      (CommAlgCat.FiniteEtale.baseChange.{u, u, u} R K).obj B => φ.hom.hom (1 ⊗ₜ[R] a)) h
  change (Algebra.TensorProduct.map (AlgHom.id K K) f.hom.hom) (1 ⊗ₜ[R] a) =
    (Algebra.TensorProduct.map (AlgHom.id K K) g.hom.hom) (1 ⊗ₜ[R] a) at h1
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul] at h1
  simp only [AlgHom.coe_id, id_eq] at h1
  exact Module.Flat.tensorProduct_mk_injective R B.obj K h1

/-- The opposite-category form of the preceding faithfulness result. -/
theorem S1760BaseChangeFunctor_faithful :
    (S1760BaseChangeFunctor R K).Faithful := by
  haveI : (CommAlgCat.FiniteEtale.baseChange.{u, u, u} R K).Faithful :=
    S1760BaseChange_faithful R K
  unfold S1760BaseChangeFunctor
  infer_instance

/-- The asserted algebraic category equivalence. -/
def S1760BaseChangeEquivalence : Prop :=
  (S1760BaseChangeFunctor R K).IsEquivalence

/-- The fullness half. -/
def S1760BaseChangeFull : Prop :=
  (S1760BaseChangeFunctor R K).Full

/-- The essential-surjectivity half.  This is false for the naive target (all
finite etale K-algebras); see the module docstring. -/
def S1760BaseChangeEssSurj : Prop :=
  (S1760BaseChangeFunctor R K).EssSurj

theorem S1760BaseChangeEquivalence_iff :
    S1760BaseChangeEquivalence R K ↔
      (S1760BaseChangeFunctor R K).Faithful ∧
        S1760BaseChangeFull R K ∧ S1760BaseChangeEssSurj R K := by
  unfold S1760BaseChangeEquivalence S1760BaseChangeFull S1760BaseChangeEssSurj
  exact ⟨fun h => ⟨h.faithful, h.full, h.essSurj⟩,
    fun h => { faithful := h.1, full := h.2.1, essSurj := h.2.2 }⟩

/-- Unconditional algebraic classification of a finite etale K-algebra: it
is a finite product of finite separable field extensions of K.  This is the
disconnected-to-finite-products half of the asserted correspondence. -/
theorem S1760FiniteEtaleAlgebraDecomposition (A : CommAlgCat.FiniteEtale.{u} K) :
    ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u)
      (_ : ∀ i, Field (Ai i)) (_ : ∀ i, Algebra K (Ai i))
      (e : A.obj ≃ₐ[K] Π i, Ai i),
      ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) :=
  (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := A.obj)).mp A.property.right

/-- The missing normal-base integral-descent lemma.  For a normal domain R,
a finite etale R-algebra B, and x in K (x)_R B integral over R, x lies in B.
This is the algebraic form of "finite etale over a normal base is normal", and
is not available in Mathlib 4.32.2.  It is the exact input that would give
fullness of the base-change comparison. -/
def S1760BaseIntegralDescent : Prop :=
  ∀ (B : CommAlgCat.FiniteEtale.{u, u} R) {x : K ⊗[R] B.obj},
    IsIntegral R x → ∃ b : B.obj,
      (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B.obj)) b = x

/-- A normal affine curve: the coordinate ring is integrally closed.  This is a
ring-level hypothesis on the base curve, not a proved fact about the concrete
Weierstrass model (which is not normal in characteristic two). -/
def S1760NormalAffineCurve : Prop :=
  IsIntegrallyClosed R

end Algebra

/-! ## 3. The general affine Spec/Gamma comparison -/

section Affine

variable (R : Type u) [CommRing R]

/-- The general affine Spec/Gamma equivalence.  Every finite etale cover of
Spec R is affine and is Spec of a finite etale R-algebra.  The field case is
proved in Example36SpecCoverEquivalenceFinal; the general case is not in
Mathlib 4.32.2.  This structure is a precise missing datum, with no inhabitant
constructed here. -/
structure S1760AffineCoverAlgebraEquivalence where
  equivalence : FiniteEtaleCover (Spec (CommRingCat.of R)) ≌
    (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ

variable {K : Type u} [Field K] [IsDomain R] [Algebra R K] [IsFractionRing R K]

/-- Conditional on the missing affine Spec/Gamma equivalence, the function-field
comparison for an affine curve is the composite of the cover/algebra comparison
and the base-change comparison. -/
noncomputable def S1760AffineFunctionFieldFunctor
    (E : S1760AffineCoverAlgebraEquivalence R) :
    FiniteEtaleCover (Spec (CommRingCat.of R)) ⥤
      (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ :=
  E.equivalence.functor ⋙ S1760BaseChangeFunctor R K

/-- The affine function-field comparison is faithful, unconditionally on the
missing affine equivalence. -/
theorem S1760AffineFunctionFieldFunctor_faithful
    (E : S1760AffineCoverAlgebraEquivalence R) :
    (S1760AffineFunctionFieldFunctor (R := R) (K := K) E).Faithful := by
  haveI : E.equivalence.functor.Faithful := E.equivalence.faithful_functor
  haveI : (S1760BaseChangeFunctor R K).Faithful :=
    S1760BaseChangeFunctor_faithful R K
  unfold S1760AffineFunctionFieldFunctor
  infer_instance

/-- The asserted equivalence for the affine function-field comparison. -/
def S1760AffineFunctionFieldEquivalence
    (E : S1760AffineCoverAlgebraEquivalence R) : Prop :=
  (S1760AffineFunctionFieldFunctor (R := R) (K := K) E).IsEquivalence

theorem S1760AffineFunctionFieldEquivalence_iff
    (E : S1760AffineCoverAlgebraEquivalence R) :
    S1760AffineFunctionFieldEquivalence (R := R) (K := K) E ↔
      (S1760AffineFunctionFieldFunctor (R := R) (K := K) E).Full ∧
        (S1760AffineFunctionFieldFunctor (R := R) (K := K) E).EssSurj := by
  unfold S1760AffineFunctionFieldEquivalence
  exact ⟨fun h => ⟨h.full, h.essSurj⟩,
    fun h => { faithful := S1760AffineFunctionFieldFunctor_faithful (R := R) (K := K) E, full := h.1, essSurj := h.2 }⟩

end Affine

/-! ## 4. The actual once-punctured curve and its function-field functor -/

section Curve

variable (F' : Type u) [Field F']

/-- The function field K = F'(E') of the actual affine once-punctured
Weierstrass curve E' = curveScheme F' = Spec F'[x,y]/(y^2-x^3+x). -/
abbrev S1760CurveFunctionField : Type u :=
  (Spec (CommRingCat.of (curveCoordinateRing F'))).functionField

instance S1760CurveFunctionField_field : Field (S1760CurveFunctionField F') :=
  inferInstance

instance S1760CurveScheme_reduced : IsReduced (curveScheme F') := inferInstance

instance S1760CurveScheme_integral : IsIntegral (curveScheme F') :=
  isIntegral_of_irreducibleSpace_of_isReduced (curveScheme F')

/-- The generic-fibre comparison for the actual once-punctured curve. -/
noncomputable def S1760CurveGenericFiberFunctor :
    FiniteEtaleCover (curveScheme F') ⥤
      (CommAlgCat.FiniteEtale.{u} (S1760CurveFunctionField F'))ᵒᵖ :=
  S1760GenericFiberFunctor (curveScheme F')

/-- The asserted equivalence for the once-punctured curve. -/
def S1760CurveGenericFiberEquivalence : Prop :=
  (S1760CurveGenericFiberFunctor F').IsEquivalence

/-- The exact decomposition of the asserted curve equivalence. -/
theorem S1760CurveGenericFiberEquivalence_iff :
    S1760CurveGenericFiberEquivalence F' ↔
      (S1760CurveGenericFiberFunctor F').Faithful ∧
        (S1760CurveGenericFiberFunctor F').Full ∧
          (S1760CurveGenericFiberFunctor F').EssSurj := by
  simpa [S1760CurveGenericFiberEquivalence, S1760CurveGenericFiberFunctor,
    S1760GenericFiberEquivalence, S1760GenericFiberFull, S1760GenericFiberEssSurj]
    using S1760GenericFiberEquivalence_iff (curveScheme F')

/-- The algebraic function field of the actual once-punctured curve, taken as
the fraction field of its coordinate ring.  It is canonically the same field as
the scheme-theoretic function field S1760CurveFunctionField. -/
abbrev S1760CurveAlgebraFunctionField : Type u :=
  FractionRing (curveCoordinateRing F')

/-- The algebraic base-change comparison for the coordinate ring of the actual
once-punctured curve. -/
noncomputable def S1760CurveAlgebraFunctor :
    (CommAlgCat.FiniteEtale.{u} (curveCoordinateRing F'))ᵒᵖ ⥤
      (CommAlgCat.FiniteEtale.{u} (S1760CurveAlgebraFunctionField F'))ᵒᵖ :=
  S1760BaseChangeFunctor (curveCoordinateRing F') (S1760CurveAlgebraFunctionField F')

/-- The algebraic comparison for the actual curve is faithful, unconditionally:
a map of finite etale algebras over the coordinate ring is determined by its
base change to K = F'(E'). -/
theorem S1760CurveAlgebraFunctor_faithful :
    (S1760CurveAlgebraFunctor F').Faithful := by
  haveI : (CommAlgCat.FiniteEtale.baseChange.{u, u, u}
      (curveCoordinateRing F') (S1760CurveAlgebraFunctionField F')).Faithful :=
    S1760BaseChange_faithful (curveCoordinateRing F') (S1760CurveAlgebraFunctionField F')
  unfold S1760CurveAlgebraFunctor S1760BaseChangeFunctor
  infer_instance

end Curve

/-! ## 5. What is missing -/

section Missing

/-- The first missing mathematical statement for the scheme-theoretic
equivalence: normality of the curve and the normal-base integral-descent lemma.
The latter is stated above as S1760BaseIntegralDescent; this abbreviation
records the intended normal curve hypothesis at the ring level. -/
def S1760CurveNormalityMissing (F' : Type u) [Field F'] : Prop :=
  IsIntegrallyClosed (curveCoordinateRing F')

/-- The first missing scheme-level statement: the general affine Spec/Gamma
equivalence for a non-field base ring.  The field case is available, the general
case is not. -/
def S1760AffineSpecGammaMissing (R : Type u) [CommRing R] : Prop :=
  Nonempty (S1760AffineCoverAlgebraEquivalence R)

/-- The first missing statement for essential surjectivity is not a lemma but a
correction of the target: the naive essential surjectivity is false, and the
correct target is the full subcategory of finite etale K-algebras whose
normalisation over the curve is finite etale.  This predicate has no
inhabitant and is recorded only to state the corrected boundary. -/
structure S1760UnramifiedFiniteEtaleSubcategory
    (X : Scheme.{u}) [IsIntegral X] where
  /-- The full subcategory of finite etale K-algebras unramified over X. -/
  fullSubcategory : (CommAlgCat.FiniteEtale.{u} (S1760FunctionField X))ᵒᵖ → Prop
  /-- The generic-fibre functor lands in this subcategory. -/
  genericFiber_mem : ∀ C : FiniteEtaleCover X,
    fullSubcategory ((S1760GenericFiberFunctor X).obj C)
  /-- The corrected equivalence target. -/
  correctedEquivalence :
    FiniteEtaleCover X ≌ ObjectProperty.FullSubcategory fullSubcategory

end Missing

/-! ## 6. Checks -/

#check S1760GenericPointMap
#check S1760GenericFiberFunctor
#check S1760GenericFiberFunctor_obj
#check S1760GenericFiberEquivalence_iff
#check S1760BaseChangeFunctor
#check S1760BaseChange_faithful
#check S1760BaseChangeFunctor_faithful
#check S1760BaseChangeEquivalence_iff
#check S1760FiniteEtaleAlgebraDecomposition
#check S1760ConnectedGenericFiberIsField
#check S1760FieldGenericFiberConnected
#check S1760BaseIntegralDescent
#check S1760AffineCoverAlgebraEquivalence
#check S1760AffineFunctionFieldFunctor_faithful
#check S1760CurveGenericFiberFunctor
#check S1760CurveGenericFiberEquivalence_iff
#check S1760CurveAlgebraFunctor
#check S1760CurveAlgebraFunctor_faithful
#check S1760CurveNormalityMissing
#check S1760AffineSpecGammaMissing
#check S1760UnramifiedFiniteEtaleSubcategory

#print axioms S1760GenericFiberFunctor_obj
#print axioms S1760BaseChange_faithful
#print axioms S1760AffineFunctionFieldFunctor_faithful

end LeanFormal.IUT.XiFPaper.S1760FunctionFieldCoversActual