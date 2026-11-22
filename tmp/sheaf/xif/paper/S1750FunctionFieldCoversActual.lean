import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# S1750 -- finite etale covers of the punctured E' and finite etale K-algebras

For the actual curve E' = S1720Curve over F' = S1720Field, let
R = F'[E' minus O] be the coordinate ring of the affine Weierstrass model
(the complement of the puncture O) and K = F'(E') = Frac R its function
field.

The naive equivalence "finite etale covers of E' minus O <-> all finite
etale K-algebras" is FALSE: a finite separable extension L/K can ramify at
a closed point of E' minus O, and then its normalization is finite flat but
not finite etale.  Example: A^1 with L = k(t)[sqrt(t)] (char != 2), which
ramifies at t = 0; for E' the same happens for K(sqrt(x)) at a point where
the x-coordinate has order 1.

The correct statements are:

* the generic-fiber functor S1750GenericFiber : covers -> finite etale
  K-algebras is faithful (proved below);
* the exact first missing theorem is fullness of this functor (a finite
  etale cover of a normal curve is determined by its generic fiber);
* the exact second missing theorem is the essential-image description: the
  image consists exactly of the finite etale K-algebras whose integral
  closure in R is finite etale over R (the unramified algebras);
* hence the corrected equivalence is onto the unramified subcategory, not
  onto all finite etale K-algebras.

On the algebra side Mathlib gives the full disconnected decomposition:
every finite etale K-algebra is a finite product of finite separable field
extensions, indexed by its finite set of maximal ideals.  This is proved in
S1750_finiteEtaleAlg_decomposition; the converse is
S1750_prod_separable_fields_finiteEtale.

Mathlib (v4.32.2) has Scheme.functionField, CommAlgCat.FiniteEtale,
FiniteEtale.baseChange, Algebra.Etale.iff_exists_algEquiv_prod, the relative
normalization, and IsIntegrallyClosed for rings.  It does NOT have a
predicate Scheme.IsNormal, the generic-fiber fullness/normalization
theorems, or the generic-fiber equivalence.  No sorry, axiom or fake
equivalence is used below; the missing statements are plain defs of
propositions.
-/

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open AlgebraicGeometry
open CategoryTheory
open scoped TensorProduct

namespace LeanFormal.IUT.XiFPaper.S1750FunctionFieldCoversActual

/-! ## 1. The actual data -/

abbrev S1750BaseField : Type := S1720Field

abbrev S1750Curve : PuncturedEllipticCurve S1750BaseField := S1720Curve

abbrev S1750AffineModel := S1750Curve.curve.toAffine

/-- The coordinate ring R = F'[E' minus O]. -/
abbrev S1750CoordinateRing : Type := S1750AffineModel.CoordinateRing

/-- The affine scheme Spec R: the punctured curve E' minus O. -/
abbrev S1750PuncturedScheme : Scheme := Spec (CommRingCat.of S1750CoordinateRing)

/-- The function field K = F'(E') = Frac R. -/
abbrev S1750FunctionField : Type := S1750AffineModel.FunctionField

theorem S1750FunctionField_eq_fractionRing :
    S1750FunctionField = FractionRing S1750CoordinateRing := rfl

instance : Field S1750FunctionField := inferInstance

/-- R is a domain, since it embeds into its fraction field K. -/
instance : IsDomain S1750CoordinateRing :=
  (IsFractionRing.injective S1750CoordinateRing S1750FunctionField).isDomain

instance : Algebra S1750CoordinateRing S1750FunctionField := inferInstance

instance : IsFractionRing S1750CoordinateRing S1750FunctionField := inferInstance

instance : FaithfulSMul S1750CoordinateRing S1750FunctionField :=
  (faithfulSMul_iff_algebraMap_injective
    S1750CoordinateRing S1750FunctionField).mpr
    (IsFractionRing.injective S1750CoordinateRing S1750FunctionField)

/-! ## 2. Finite etale algebras over K -/

abbrev S1750FiniteEtaleAlg : Type 1 :=
  (CommAlgCat.FiniteEtale.{0} S1750FunctionField)ᵒᵖ

instance S1750MaximalSpectrumFinite
    (A : CommAlgCat.FiniteEtale.{0} S1750FunctionField) :
    Finite (MaximalSpectrum A.obj) := inferInstance

instance S1750QuotientField
    (A : CommAlgCat.FiniteEtale.{0} S1750FunctionField)
    (I : MaximalSpectrum A.obj) :
    Field (A.obj ⧸ I.asIdeal) :=
  Ideal.Quotient.field I.asIdeal

/-- Every finite etale K-algebra is canonically a finite product of finite
separable field extensions, indexed by its finite set of maximal ideals.
This is the algebra-side disconnected decomposition. -/
theorem S1750_finiteEtaleAlg_decomposition
    (A : CommAlgCat.FiniteEtale.{0} S1750FunctionField) :
    ∃ _e : A.obj ≃ₐ[S1750FunctionField]
        (∀ I : MaximalSpectrum A.obj, A.obj ⧸ I.asIdeal),
      Finite (MaximalSpectrum A.obj) ∧
      (∀ I : MaximalSpectrum A.obj,
        Module.Finite S1750FunctionField (A.obj ⧸ I.asIdeal)) ∧
      (∀ I : MaximalSpectrum A.obj,
        Algebra.IsSeparable S1750FunctionField (A.obj ⧸ I.asIdeal)) := by
  haveI : IsReduced A.obj :=
    Algebra.FormallyUnramified.isReduced_of_field S1750FunctionField A.obj
  refine ⟨(IsArtinianRing.equivPi A.obj).restrictScalars S1750FunctionField,
    inferInstance, ?_, ?_⟩
  · intro I
    infer_instance
  · intro I
    infer_instance

/-- Conversely, every finite product of finite separable field extensions
of K is a finite etale K-algebra. -/
theorem S1750_prod_separable_fields_finiteEtale
    {I : Type} [Fintype I] (Ai : I → Type) [∀ i, Field (Ai i)]
    [∀ i, Algebra S1750FunctionField (Ai i)]
    [∀ i, Module.Finite S1750FunctionField (Ai i)]
    [∀ i, Algebra.IsSeparable S1750FunctionField (Ai i)] :
    ∃ A : CommAlgCat.FiniteEtale.{0} S1750FunctionField,
      Nonempty (A.obj ≃ₐ[S1750FunctionField] Π i, Ai i) := by
  haveI : Algebra.Etale S1750FunctionField (Π i, Ai i) := by
    haveI : ∀ i, Algebra.Etale S1750FunctionField (Ai i) := by
      intro i
      haveI : Module.FinitePresentation S1750FunctionField (Ai i) :=
        Module.finitePresentation_of_finite S1750FunctionField _
      exact
        { formallyEtale :=
            Algebra.FormallyEtale.of_isSeparable S1750FunctionField (Ai i),
          finitePresentation :=
            Algebra.FinitePresentation.of_finitePresentation S1750FunctionField _ }
    infer_instance
  exact ⟨CommAlgCat.FiniteEtale.of S1750FunctionField (Π i, Ai i),
    ⟨AlgEquiv.refl⟩⟩

/-- A nontrivial finite etale K-algebra is a field iff its prime spectrum
is a singleton.  A field is the algebra-side connected object. -/
theorem S1750_isField_iff_subsingleton_primeSpectrum
    (A : CommAlgCat.FiniteEtale.{0} S1750FunctionField) [Nontrivial A.obj] :
    IsField A.obj ↔ Subsingleton (PrimeSpectrum A.obj) := by
  haveI : IsReduced A.obj :=
    Algebra.FormallyUnramified.isReduced_of_field S1750FunctionField A.obj
  exact (PrimeSpectrum.subsingleton_iff_isField_of_isReduced (R := A.obj)).symm

/-! ## 3. Covers and the generic-fiber functor -/

/-- The affine finite etale cover category of the punctured curve:
finite etale R-algebras, opposite to make the generic-fiber functor
covariant. -/
abbrev S1750FiniteEtaleCover : Type 1 :=
  (CommAlgCat.FiniteEtale.{0} S1750CoordinateRing)ᵒᵖ

/-- The generic-fiber functor: base change from R to K = Frac R. -/
abbrev S1750GenericFiber : S1750FiniteEtaleCover ⥤ S1750FiniteEtaleAlg :=
  (CommAlgCat.FiniteEtale.baseChange
    S1750CoordinateRing S1750FunctionField).op

/-- The generic-fiber functor is faithful: a morphism of finite etale
R-algebras is determined by its base change to K. -/
instance S1750BaseChange_faithful :
    (CommAlgCat.FiniteEtale.baseChange
      S1750CoordinateRing S1750FunctionField).Faithful := by
  refine ⟨?_⟩
  intro A B f g h
  ext a
  have h1 := congrArg
    (fun φ : (CommAlgCat.FiniteEtale.baseChange
        S1750CoordinateRing S1750FunctionField).obj A ⟶
        (CommAlgCat.FiniteEtale.baseChange
          S1750CoordinateRing S1750FunctionField).obj B =>
      φ.hom.hom (1 ⊗ₜ[S1750CoordinateRing] a)) h
  change
    (Algebra.TensorProduct.map (AlgHom.id S1750FunctionField S1750FunctionField)
      f.hom.hom) (1 ⊗ₜ[S1750CoordinateRing] a) =
    (Algebra.TensorProduct.map (AlgHom.id S1750FunctionField S1750FunctionField)
      g.hom.hom) (1 ⊗ₜ[S1750CoordinateRing] a) at h1
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul] at h1
  simp only [AlgHom.coe_id, id_eq] at h1
  exact Module.Flat.tensorProduct_mk_injective
    S1750CoordinateRing B.obj S1750FunctionField h1

instance S1750GenericFiber_faithful : S1750GenericFiber.Faithful :=
  inferInstanceAs ((CommAlgCat.FiniteEtale.baseChange
    S1750CoordinateRing S1750FunctionField).op.Faithful)

/-! ## 4. The exact missing theorems -/

@[reducible] def S1750RestrictScalars (A : S1750FiniteEtaleAlg) :
    Algebra S1750CoordinateRing A.unop.obj :=
  RingHom.toAlgebra
    ((algebraMap S1750FunctionField A.unop.obj).comp
      (algebraMap S1750CoordinateRing S1750FunctionField))

/-- The integral closure of R in A. -/
def S1750IntegralModel (A : S1750FiniteEtaleAlg) :=
  letI := S1750RestrictScalars A
  integralClosure S1750CoordinateRing A.unop.obj

/-- A is unramified on E' minus O: its integral closure in A is finite
etale over R. -/
def S1750Unramified (A : S1750FiniteEtaleAlg) : Prop :=
  Module.Finite S1750CoordinateRing (S1750IntegralModel A) ∧
  Algebra.Etale S1750CoordinateRing (S1750IntegralModel A)

def S1750InGenericFiberImage (A : S1750FiniteEtaleAlg) : Prop :=
  ∃ B : S1750FiniteEtaleCover,
    Nonempty (S1750GenericFiber.obj B ≅ A)

/-- R is integrally closed.  True for the affine model of a smooth curve,
but not proved in Mathlib for the Weierstrass coordinate ring. -/
def S1750NormalityMissing : Prop := IsIntegrallyClosed S1750CoordinateRing

/-- EXACT FIRST MISSING THEOREM: the generic-fiber functor is full.  This
is the "finite etale covers of a normal curve are determined by their
generic fiber" extension theorem. -/
def S1750FirstMissing : Prop := S1750GenericFiber.Full

/-- EXACT SECOND MISSING THEOREM: the essential image of the generic-fiber
functor is exactly the unramified finite etale K-algebras. -/
def S1750SecondMissing : Prop :=
  ∀ A : S1750FiniteEtaleAlg,
    S1750InGenericFiberImage A ↔ S1750Unramified A

/-- The corrected equivalence, conditional on the two missing theorems. -/
def S1750CorrectedEquivalence : Prop :=
  S1750FirstMissing ∧ S1750SecondMissing

/-- The naive "all finite etale K-algebras" statement, recorded only for
comparison.  It is FALSE; see the module docstring. -/
def S1750NaiveEquivalence : Prop :=
  ∀ A : S1750FiniteEtaleAlg, S1750InGenericFiberImage A

/-- The generic fiber of a cover is a field. -/
def S1750GenericFiberIsField (B : S1750FiniteEtaleCover) : Prop :=
  IsField (S1750GenericFiber.obj B).unop.obj

/-- Corrected connected correspondence. -/
def S1750ConnectedCorrespondence : Prop :=
  ∀ A : S1750FiniteEtaleAlg,
    S1750Unramified A →
      (IsField A.unop.obj ↔
        ∃ B : S1750FiniteEtaleCover,
          S1750GenericFiberIsField B ∧
            Nonempty (S1750GenericFiber.obj B ≅ A))

/-- The proved disconnected decomposition, restated as a proposition. -/
def S1750DisconnectedDecomposition : Prop :=
  ∀ A : CommAlgCat.FiniteEtale.{0} S1750FunctionField,
    ∃ _e : A.obj ≃ₐ[S1750FunctionField]
        (∀ I : MaximalSpectrum A.obj, A.obj ⧸ I.asIdeal),
      Finite (MaximalSpectrum A.obj) ∧
      (∀ I : MaximalSpectrum A.obj,
        Module.Finite S1750FunctionField (A.obj ⧸ I.asIdeal)) ∧
      (∀ I : MaximalSpectrum A.obj,
        Algebra.IsSeparable S1750FunctionField (A.obj ⧸ I.asIdeal))

theorem S1750DisconnectedDecomposition_true :
    S1750DisconnectedDecomposition :=
  S1750_finiteEtaleAlg_decomposition

/-! ## 5. Axiom footprint -/

#print axioms S1750FunctionField_eq_fractionRing
#print axioms S1750BaseChange_faithful
#print axioms S1750GenericFiber_faithful
#print axioms S1750_finiteEtaleAlg_decomposition
#print axioms S1750_prod_separable_fields_finiteEtale
#print axioms S1750_isField_iff_subsingleton_primeSpectrum
#print axioms S1750DisconnectedDecomposition_true

end LeanFormal.IUT.XiFPaper.S1750FunctionFieldCoversActual
