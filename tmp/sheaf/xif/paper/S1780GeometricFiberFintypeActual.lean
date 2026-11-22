/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1735GeometricFiberActual
import tmp.sheaf.xif.paper.S1733EssentiallySmallCoversActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import Mathlib.RingTheory.Artinian.Module

/-!
# S1780: finiteness of the literal geometric fiber at the actual S1726 point (0,0)

## Question

S1735 records the exact finiteness input for the actual geometric fiber functor of
the S1726 orbicurve X = S1726Orbicurve over F' = S1726K:

  S1735GeometricFiberFintypeRequired :=
    forall cover, Nonempty (Fintype (GeometricFiber S1735BaseScheme S1735BasePoint cover))

The task here is to prove it from the representability / base-change property of
EtaleStackFiniteEtaleMorphism, by comparing the literal CostructuredArrow geometric
fiber with the scheme-theoretic finite fiber of the base-change model, and to state
the exact first missing input if the proof does not close.

## What this file proves (no sorry, no axiom)

* S1780BaseChange: the actual base-change presentation of a cover at the actual
  point (0,0) -- this is precisely the finite-etale representability datum of
  cover.finiteEtale, not an extra assumption;
* S1780Model / S1780ModelOver: the scheme-theoretic model and its structure
  morphism, proved IsFinite and Etale over the actual base Spec F'
  (S1780Model_finiteEtale) -- this is the scheme-theoretic finite fiber side;
* S1780BaseEndomorphism_subsingleton and S1780_section_comp_projection: the actual
  base object Over.mk (id (Spec F')) is the terminal object, so every composite of
  a section of the model with its projection is the identity.  This is what lets
  the 2-commuting square of the base change be evaluated at the identity section;
* S1780SubsingletonAlgHomOfField: two K-algebra maps from a field extension into K
  coincide (no finiteness needed);
* S1780AlgHomFintype: for a finite algebra A over a field K, the type of K-algebra
  maps A ->_alg[K] K is finite.  This is the algebraic core of the finiteness of the
  scheme-theoretic fiber: sections of a finite scheme over Spec K are K-algebra maps
  out of its ring of global sections;
* S1780SectionToFiber: the comparison map from sections of the base-change model to
  objects of the literal geometric fiber, built from the commuting 2-cell of the
  base-change presentation and from the terminality of the actual base;
* S1780FintypeRequired_of_comparison: if every object of the literal geometric fiber
  is the image of a section of the base-change model and the section type is finite,
  then the target statement holds.

## Exact first missing

The unconditional statement is not obtained.  In dependency order the missing
inputs are:

1. S1780SectionFintype cover: the type of sections S1735BaseScheme -> S1780Model
   cover is finite.  The file proves the algebraic core (S1780AlgHomFintype) and the
   representability datum (S1780Model_finiteEtale); the remaining bridge is the
   affine-sections identification (S -> X) ~ (Gamma(X, top) ->_alg[K] K) for X
   finite over Spec K.  The appTop map gives one direction and
   Scheme.isoSpec_hom_naturality gives injectivity, so this bridge is Mathlib-level
   bookkeeping over Gamma(Spec K) ~ K, not a geometric hypothesis.

2. S1780FiberCovered cover: every object of the literal geometric fiber is the image
   of a section of the base-change model, i.e. S1780SectionToFiber is surjective.
   This is the object-level content of the two-pullback universal property.  The
   TwoPullbackWitness of EtaleStackFiniteEtaleMorphism is a cone-level statement:
   its essential surjectivity is stated for strong transformations from a
   pseudofunctor, not for objects of the fiber category at a single test scheme, and
   evaluating it at the base object requires the pseudofunctor Yoneda comparison
   StrongTrans (Y S) F ~ F(S) on top of it.  This is the first genuinely missing
   geometric/categorical theorem.

In particular no geometricity of the base point is needed: Spec F' is not a
geometric point (F' is not separably closed), but the fiber of a finite etale cover
over a scheme-valued point is a finite etale scheme over Spec F', and its sections
-- equivalently the K-algebra maps out of a finite F'-algebra -- are finite by
S1780AlgHomFintype regardless of the residue field.  An algebraically closed residue
field would not remove gap 2.

No fiber, no Fintype instance, no equivalence and no finiteness statement is faked;
every Fintype produced below is transported from S1780AlgHomFintype or is an
explicit hypothesis.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1780GeometricFiberFintypeActual

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual.Paper

universe u v w

/-! ## 1. The actual base-change model at the point (0,0) -/

/-- The actual base change of a cover along the actual point (0,0): this is the
finite-etale representability datum of cover.finiteEtale itself, not an extra
assumption. -/
noncomputable def S1780BaseChange (cover : S1735Cover) :
    EtaleStackBaseChangePresentation cover.map S1735BaseScheme S1735BasePoint :=
  cover.finiteEtale.baseChange S1735BaseScheme S1735BasePoint

/-- The scheme-theoretic model of a cover at the actual point: the base change
Spec F' x_X source of the cover. -/
noncomputable abbrev S1780Model (cover : S1735Cover) : SchemeOverField S1735K :=
  (S1780BaseChange cover).pullbackScheme

/-- The structure morphism of the model to the actual base Spec F'. -/
noncomputable abbrev S1780ModelOver (cover : S1735Cover) :
    S1780Model cover ⟶ S1735BaseScheme :=
  (S1780BaseChange cover).projection

/-- The scheme-theoretic finite fiber is finite etale over the actual base.  This
is the representability half of EtaleStackFiniteEtaleMorphism, read at the actual
point (0,0); it is unconditional. -/
theorem S1780Model_finiteEtale (cover : S1735Cover) :
    IsFinite (S1780ModelOver cover).left ∧ Etale (S1780ModelOver cover).left :=
  cover.finiteEtale.hasProperty S1735BaseScheme S1735BasePoint

/-- Every endomorphism of the actual base object is the identity: S1735BaseScheme
is Over.mk (id (Spec F')), the terminal object of Over (Spec F'). -/
theorem S1780BaseEndomorphism_subsingleton :
    Subsingleton (S1735BaseScheme ⟶ S1735BaseScheme) :=
  ⟨fun f g => Over.mkIdTerminal.hom_ext f g⟩

/-- Composing a section of the base-change model with its projection gives the
identity of the base.  This is the computation that identifies the target of the
commuting 2-cell with the point object of the geometric fiber. -/
theorem S1780_section_comp_projection (cover : S1735Cover)
    (s : S1735BaseScheme ⟶ S1780Model cover) :
    s ≫ S1780ModelOver cover = 𝟙 S1735BaseScheme :=
  @Subsingleton.elim _ S1780BaseEndomorphism_subsingleton _ _

/-! ## 2. The algebraic core: K-algebra maps out of a finite K-algebra -/

section Algebra

variable (K : Type u) [Field K]

/-- Two K-algebra maps from a field extension of K into K coincide.  No finiteness
is needed: a K-algebra map L ->_alg[K] K forces algebraMap K L to be surjective,
hence L = K and the map is the inverse of algebraMap. -/
theorem S1780SubsingletonAlgHomOfField (L : Type u) [Field L] [Algebra K L] :
    Subsingleton (L →ₐ[K] K) := by
  constructor
  intro φ ψ
  ext x
  have hinj : Function.Injective (φ : L → K) := φ.toRingHom.injective
  have hφ : algebraMap K L (φ x) = x := by
    apply hinj
    rw [AlgHom.commutes]
    simp
  have hψ : ψ x = φ x := by
    conv_lhs => rw [← hφ]
    rw [AlgHom.commutes]
    simp
  exact hψ.symm

/-- For a finite algebra A over a field K, the K-algebra maps A ->_alg[K] K form a
finite type.  The proof injects such a map into its kernel, a maximal ideal of the
Artinian ring A; there are finitely many of those, and two maps with the same
kernel agree because both factor through the residue field, where
S1780SubsingletonAlgHomOfField applies. -/
@[reducible] noncomputable def S1780AlgHomFintype (A : Type u) [CommRing A] [Algebra K A]
    [Module.Finite K A] : Fintype (A →ₐ[K] K) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have hkerIsPrime : ∀ φ : A →ₐ[K] K, (RingHom.ker φ.toRingHom).IsPrime :=
    fun φ => RingHom.ker_isPrime φ.toRingHom
  refine Fintype.ofInjective
    (fun φ : A →ₐ[K] K =>
      (⟨RingHom.ker φ.toRingHom, ?_⟩ : MaximalSpectrum A)) ?_
  · haveI := hkerIsPrime φ
    infer_instance
  · intro φ ψ h
    have hker : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom :=
      congrArg MaximalSpectrum.asIdeal h
    have hker' : ∀ a : A, φ a = 0 ↔ ψ a = 0 := by
      intro a
      have h1 : a ∈ RingHom.ker φ.toRingHom ↔ a ∈ RingHom.ker ψ.toRingHom := by
        rw [hker]
      exact ⟨fun h => RingHom.mem_ker.mpr (h1.mp (RingHom.mem_ker.mp h)),
        fun h => RingHom.mem_ker.mpr (h1.mpr (RingHom.mem_ker.mp h))⟩
    ext x
    by_cases hx : φ x = 0
    · rw [hx, (hker' x).mp hx]
    · have hφ1 : φ ((φ x) • (1 : A)) = φ x := by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, map_one]
        simp
      have hψ1 : ψ ((φ x) • (1 : A)) = φ x := by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, map_one]
        simp
      have hy : φ ((φ x) • (1 : A) - x) = 0 := by
        rw [map_sub, hφ1, sub_self]
      have hy2 : ψ ((φ x) • (1 : A) - x) = 0 := (hker' _).mp hy
      rw [map_sub, hψ1] at hy2
      exact sub_eq_zero.mp hy2

end Algebra

/-! ## 3. The comparison map: sections of the model to objects of the geometric fiber -/

/-- The test object at which the literal geometric fiber is taken. -/
noncomputable abbrev S1780Site : LocallyDiscrete (SchemeOverField S1735K)ᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S1735BaseScheme)

/-- The point object of the geometric fiber: the object of the orbicurve stack at
the actual base selected by the actual point (0,0). -/
noncomputable abbrev S1780PointObject :
    (S1735Orbicurve.stack.fiber).obj S1780Site :=
  OrbicurveFiniteEtaleCover.pointObject S1735BaseScheme S1735BasePoint

/-- The object of the cover stack at the actual base attached to a section of the
base-change model, via the first leg of the base-change square. -/
noncomputable def S1780SectionStackObject (cover : S1735Cover)
    (s : S1735BaseScheme ⟶ S1780Model cover) :
    (cover.source.fiber).obj S1780Site :=
  ((S1780BaseChange cover).toSource.app S1780Site).toFunctor.obj (Discrete.mk s)

/-- The projection of the base-change model acts on the identity section as the
identity of the base, because the base object is terminal. -/
theorem S1780_projection_identity_section (cover : S1735Cover)
    (s : S1735BaseScheme ⟶ S1780Model cover) :
    ((S1780BaseChange cover).projectionMap.transformation.app S1780Site).toFunctor.obj
        (Discrete.mk s) =
      Discrete.mk (𝟙 S1735BaseScheme) := by
  rw [SchemeRepresentableMap.app_eq]
  show Discrete.mk (s ≫ S1780ModelOver cover) = Discrete.mk (𝟙 S1735BaseScheme)
  rw [S1780_section_comp_projection]

/-- The commuting 2-cell of the base-change presentation, evaluated at a section of
the model, gives an object of the literal geometric fiber. -/
noncomputable def S1780SectionToFiber (cover : S1735Cover)
    (s : S1735BaseScheme ⟶ S1780Model cover) : S1735Fiber cover := by
  classical
  let B := S1780BaseChange cover
  let comp :
      (B.toSource.app S1780Site ≫ cover.map.app S1780Site) ⟶
        (B.projectionMap.transformation.app S1780Site ≫ S1735BasePoint.app S1780Site) :=
    eqToHom (Pseudofunctor.StrongTrans.comp_app B.toSource cover.map S1780Site).symm
      ≫ B.commutes.hom.as.app S1780Site
      ≫ eqToHom (Pseudofunctor.StrongTrans.comp_app B.projectionMap.transformation
          S1735BasePoint S1780Site)
  have hd :
      ((B.projectionMap.transformation.app S1780Site ≫
          S1735BasePoint.app S1780Site).toFunctor.obj (Discrete.mk s)) =
        S1780PointObject := by
    show (S1735BasePoint.app S1780Site).toFunctor.obj
        (((B.projectionMap.transformation.app S1780Site).toFunctor.obj
          (Discrete.mk s))) = S1780PointObject
    rw [S1780_projection_identity_section]
    rfl
  exact CostructuredArrow.mk (Y := S1780SectionStackObject cover s)
    ((comp.toNatTrans.app (Discrete.mk s)) ≫ eqToHom hd)

/-! ## 4. The exact first missing input and the reduction -/

/-- The scheme-theoretic finite fiber at the actual point is finite: sections of
the base-change model form a finite type. -/
def S1780SectionFintype (cover : S1735Cover) : Prop :=
  Nonempty (Fintype (S1735BaseScheme ⟶ S1780Model cover))

/-- Every object of the literal geometric fiber is the image of a section of the
base-change model: the object-level comparison of the geometric fiber with the
scheme-theoretic finite fiber of the base change. -/
def S1780FiberCovered (cover : S1735Cover) : Prop :=
  Function.Surjective (S1780SectionToFiber cover)

/-- The exact first missing input, as one proposition. -/
def S1780FirstMissing : Prop :=
  (∀ cover : S1735Cover, S1780SectionFintype cover) ∧
    (∀ cover : S1735Cover, S1780FiberCovered cover)

/-- From the comparison (every geometric-fiber object is the image of a section of
the base-change model) and the finiteness of the scheme-theoretic fiber, the
literal geometric fiber is finite.  Nothing here is postulated: the Fintype
instance is transported across the surjection produced by the comparison. -/
theorem S1780FintypeRequired_of_comparison
    (hfin : ∀ cover : S1735Cover, S1780SectionFintype cover)
    (hcov : ∀ cover : S1735Cover, S1780FiberCovered cover) :
    S1735GeometricFiberFintypeRequired := by
  classical
  intro cover
  haveI : Fintype (S1735BaseScheme ⟶ S1780Model cover) := Classical.choice (hfin cover)
  exact ⟨Fintype.ofSurjective (S1780SectionToFiber cover) (hcov cover)⟩

/-- The same reduction from the packaged first missing input. -/
theorem S1780FintypeRequired_of_firstMissing (h : S1780FirstMissing) :
    S1735GeometricFiberFintypeRequired :=
  S1780FintypeRequired_of_comparison h.1 h.2

/-! ## 5. Axiom footprint -/

#print axioms S1780Model_finiteEtale
#print axioms S1780BaseEndomorphism_subsingleton
#print axioms S1780_section_comp_projection
#print axioms S1780SubsingletonAlgHomOfField
#print axioms S1780AlgHomFintype
#print axioms S1780_projection_identity_section
#print axioms S1780SectionToFiber
#print axioms S1780FintypeRequired_of_comparison
#print axioms S1780FintypeRequired_of_firstMissing

end LeanFormal.IUT.XiFPaper.S1780GeometricFiberFintypeActual
