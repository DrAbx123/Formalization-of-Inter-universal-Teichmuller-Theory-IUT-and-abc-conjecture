import LeanFormal.IUT.Foundations.AlgebraicGeometry.LocalFactorCompatibilityProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientUniversalPropertyFromGluing
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Actual quotient universal property and full-G factorization

The global factor is the actual globalFactor obtained from the Q gluing
universal property.  The local-factor compatibility needed to apply it is
derived from the actual chart-overlap comparison, so the only remaining input is
the projection overlap compatibility.  No quotient universal property or factor
is assumed.
-/
namespace ABCBridge.QuotientUniversalPropertyActualFinal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GInvariantAffineQuotientCoverConstruct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiQuotientChartDatumActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientChartGluingConstruct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
open ABCBridge.QuotientUniversalPropertyFromGluing
open ABCBridge.LocalFactorCompatibilityProof

universe u

variable {R : Type u} [CommRing R]
  {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
  {G : Type u} [Group G]
  (A : GlobalQuotientActionData (R := R) X (G := G))
  {C : GInvariantAffineQuotientCover (X := X) (G := G) A}
  (HG : QuotientChartGluingData (X := X) (G := G) A C)

/-- The actual factor of a full-G-invariant morphism, using the gluing universal
property and the local-factor compatibility derived from the chart-overlap
comparison. -/
noncomputable def actualQuotientFactor
    (HC : ChartOverlapComparison (A := A) HG)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z) :
    HG.Q ⟶ Z :=
  globalFactor (A := A) HG Z f.hom
    (localFactorCompatibility_of_chartOverlapComparison (A := A) HG HC Z f.hom)

/-- The actual factor restricts to the local factors on the quotient charts. -/
theorem actualQuotientFactor_chart
    (HC : ChartOverlapComparison (A := A) HG)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z)
    (i : C.J) :
    HG.chartToQ i ≫ actualQuotientFactor (A := A) HG HC Z f =
      localFactor (A := A) HG Z f.hom i :=
  globalFactor_chart (A := A) HG Z f.hom
    (localFactorCompatibility_of_chartOverlapComparison (A := A) HG HC Z f.hom) i

/-- The actual factor composed with the projection is the original
full-G-invariant morphism. -/
theorem actualQuotientFactor_fac
    (HC : ChartOverlapComparison (A := A) HG)
    (hoverlap : HG.OverlapCompatibility)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z) :
    HG.projection hoverlap ≫ actualQuotientFactor (A := A) HG HC Z f = f.hom :=
  globalFactor_projection (A := A) HG Z f.hom hoverlap
    (localFactorCompatibility_of_chartOverlapComparison (A := A) HG HC Z f.hom)

/-- The actual factor is unique. -/
theorem actualQuotientFactor_uniq
    (HC : ChartOverlapComparison (A := A) HG)
    (hoverlap : HG.OverlapCompatibility)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z)
    (u : HG.Q ⟶ Z)
    (hu : HG.projection hoverlap ≫ u = f.hom) :
    u = actualQuotientFactor (A := A) HG HC Z f :=
  globalFactor_uniq (A := A) HG Z f.hom hoverlap
    (localFactorCompatibility_of_chartOverlapComparison (A := A) HG HC Z f.hom) u hu

/-- The actual quotient universal property: every full-G-invariant morphism
factors uniquely through the projection, with only projection overlap
compatibility as input. -/
theorem actualQuotientUniversalProperty
    (HC : ChartOverlapComparison (A := A) HG)
    (hoverlap : HG.OverlapCompatibility)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z) :
    ∃! u : HG.Q ⟶ Z, HG.projection hoverlap ≫ u = f.hom :=
  ⟨actualQuotientFactor (A := A) HG HC Z f,
    actualQuotientFactor_fac (A := A) HG HC hoverlap Z f,
    fun u hu => actualQuotientFactor_uniq (A := A) HG HC hoverlap Z f u hu⟩

/-- The actual factorization data: the projection overlap residual and the
actual factor/fac/uniq. -/
structure ActualQuotientUniversalPropertyData where
  overlap : HG.OverlapCompatibility
  factor : ∀ (Z : Scheme.{u}),
    FullGInvariantMorphism (A := A) (G := G) Z → (HG.Q ⟶ Z)
  factor_chart : ∀ (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z) (i : C.J),
    HG.chartToQ i ≫ factor Z f = localFactor (A := A) HG Z f.hom i
  factor_fac : ∀ (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z),
    HG.projection overlap ≫ factor Z f = f.hom
  factor_uniq : ∀ (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z)
    (u : HG.Q ⟶ Z),
    HG.projection overlap ≫ u = f.hom → u = factor Z f

/-- The actual data, from the chart-overlap comparison and the projection overlap
compatibility. -/
noncomputable def actualQuotientUniversalPropertyData
    (HC : ChartOverlapComparison (A := A) HG)
    (hoverlap : HG.OverlapCompatibility) :
    ActualQuotientUniversalPropertyData (A := A) HG where
  overlap := hoverlap
  factor := fun Z f => actualQuotientFactor (A := A) HG HC Z f
  factor_chart := fun Z f i => actualQuotientFactor_chart (A := A) HG HC Z f i
  factor_fac := fun Z f => actualQuotientFactor_fac (A := A) HG HC hoverlap Z f
  factor_uniq := fun Z f u hu =>
    actualQuotientFactor_uniq (A := A) HG HC hoverlap Z f u hu

/-- The actual data have only the projection overlap compatibility as residual. -/
theorem actualQuotientUniversalPropertyData_overlap
    (D : ActualQuotientUniversalPropertyData (A := A) HG) :
    HG.OverlapCompatibility :=
  D.overlap

/-- The exact compatibility residual reduces to projection overlap
compatibility. -/
theorem actualQuotientUniversalProperty_exactResidual_iff_overlap
    (HC : ChartOverlapComparison (A := A) HG) :
    ExactCompatibilityResidual (A := A) HG ↔ HG.OverlapCompatibility :=
  exactCompatibilityResidual_iff_overlap (A := A) HG HC

/-- The actual factorization with the factor exposed. -/
theorem actualQuotientUniversalPropertyData_factor_fac
    (D : ActualQuotientUniversalPropertyData (A := A) HG)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z) :
    HG.projection D.overlap ≫ D.factor Z f = f.hom :=
  D.factor_fac Z f

/-- The actual factorization is unique. -/
theorem actualQuotientUniversalPropertyData_factor_uniq
    (D : ActualQuotientUniversalPropertyData (A := A) HG)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z)
    (u : HG.Q ⟶ Z)
    (hu : HG.projection D.overlap ≫ u = f.hom) :
    u = D.factor Z f :=
  D.factor_uniq Z f u hu

/-- The actual factor is the gluing global factor; this is not a wrapper. -/
theorem actualQuotientUniversalPropertyData_factor_eq_globalFactor
    (HC : ChartOverlapComparison (A := A) HG)
    (D : ActualQuotientUniversalPropertyData (A := A) HG)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z) :
    D.factor Z f =
      globalFactor (A := A) HG Z f.hom
        (localFactorCompatibility_of_chartOverlapComparison (A := A) HG HC Z f.hom) :=
  rfl

/-- Complete actual package. -/
theorem actualQuotientUniversalProperty_complete
    (HC : ChartOverlapComparison (A := A) HG)
    (hoverlap : HG.OverlapCompatibility) :
    (∀ (Z : Scheme.{u})
      (f : FullGInvariantMorphism (A := A) (G := G) Z),
      HG.projection hoverlap ≫
          (actualQuotientUniversalPropertyData (A := A) HG HC hoverlap).factor Z f =
        f.hom) ∧
      (∀ (Z : Scheme.{u})
        (f : FullGInvariantMorphism (A := A) (G := G) Z)
        (u : HG.Q ⟶ Z),
        HG.projection hoverlap ≫ u = f.hom →
          u = (actualQuotientUniversalPropertyData (A := A) HG HC hoverlap).factor Z f) ∧
      (∀ (Z : Scheme.{u})
        (f : FullGInvariantMorphism (A := A) (G := G) Z) (i : C.J),
        HG.chartToQ i ≫
            (actualQuotientUniversalPropertyData (A := A) HG HC hoverlap).factor Z f =
          localFactor (A := A) HG Z f.hom i) :=
  ⟨fun Z f => actualQuotientUniversalPropertyData_factor_fac (A := A) HG
      (actualQuotientUniversalPropertyData (A := A) HG HC hoverlap) Z f,
    fun Z f u hu => actualQuotientUniversalPropertyData_factor_uniq (A := A) HG
      (actualQuotientUniversalPropertyData (A := A) HG HC hoverlap) Z f u hu,
    fun Z f i => (actualQuotientUniversalPropertyData (A := A) HG HC hoverlap).factor_chart Z f i⟩

/-- The actual universal property data exist exactly from the comparison and the
projection overlap compatibility. -/
theorem actualQuotientUniversalPropertyData_exists
    (HC : ChartOverlapComparison (A := A) HG)
    (hoverlap : HG.OverlapCompatibility) :
    Nonempty (ActualQuotientUniversalPropertyData (A := A) HG) :=
  ⟨actualQuotientUniversalPropertyData (A := A) HG HC hoverlap⟩


section ActualFinalProjections

/-- The actual factor is definitionally the gluing global factor. -/
theorem actualQuotientFactor_eq_globalFactor
    (HC : ChartOverlapComparison (A := A) HG)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z) :
    actualQuotientFactor (A := A) HG HC Z f =
      globalFactor (A := A) HG Z f.hom
        (localFactorCompatibility_of_chartOverlapComparison (A := A) HG HC Z f.hom) :=
  rfl

/-- The actual factor's chart restrictions for all charts. -/
theorem actualQuotientFactor_chart_all
    (HC : ChartOverlapComparison (A := A) HG)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z) :
    ∀ i : C.J,
      HG.chartToQ i ≫ actualQuotientFactor (A := A) HG HC Z f =
        localFactor (A := A) HG Z f.hom i :=
  fun i => actualQuotientFactor_chart (A := A) HG HC Z f i

/-- The actual factorization for all full-G-invariant morphisms. -/
theorem actualQuotientUniversalProperty_all
    (HC : ChartOverlapComparison (A := A) HG)
    (hoverlap : HG.OverlapCompatibility) :
    ∀ (Z : Scheme.{u})
      (f : FullGInvariantMorphism (A := A) (G := G) Z),
      ∃! u : HG.Q ⟶ Z, HG.projection hoverlap ≫ u = f.hom :=
  fun Z f => actualQuotientUniversalProperty (A := A) HG HC hoverlap Z f

/-- The actual data's chart restriction. -/
theorem actualQuotientUniversalPropertyData_factor_chart_apply
    (D : ActualQuotientUniversalPropertyData (A := A) HG)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z)
    (i : C.J) :
    HG.chartToQ i ≫ D.factor Z f = localFactor (A := A) HG Z f.hom i :=
  D.factor_chart Z f i

/-- The actual data's existential-unique factor form. -/
theorem actualQuotientUniversalPropertyData_exists_unique
    (D : ActualQuotientUniversalPropertyData (A := A) HG)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z) :
    ∃! u : HG.Q ⟶ Z, HG.projection D.overlap ≫ u = f.hom :=
  ⟨D.factor Z f, D.factor_fac Z f, fun u hu => D.factor_uniq Z f u hu⟩

/-- The actual universal property is exactly the projection overlap
compatibility. -/
def ActualQuotientUniversalProperty : Prop :=
  HG.OverlapCompatibility

/-- The actual property follows from projection overlap compatibility. -/
theorem actualQuotientUniversalProperty_of_overlap
    (hoverlap : HG.OverlapCompatibility) :
    ActualQuotientUniversalProperty (A := A) HG :=
  hoverlap

/-- The actual universal property supplies the projection overlap
compatibility. -/
theorem actualQuotientUniversalProperty_overlap
    (h : ActualQuotientUniversalProperty (A := A) HG) :
    HG.OverlapCompatibility :=
  h

/-- The actual universal property data exist from the actual property and the
chart-overlap comparison. -/
theorem actualQuotientUniversalPropertyData_of_actual
    (HC : ChartOverlapComparison (A := A) HG)
    (h : ActualQuotientUniversalProperty (A := A) HG) :
    Nonempty (ActualQuotientUniversalPropertyData (A := A) HG) :=
  actualQuotientUniversalPropertyData_exists (A := A) HG HC h

/-- The actual data factor is unique in the strong form. -/
theorem actualQuotientUniversalPropertyData_factor_unique
    (D : ActualQuotientUniversalPropertyData (A := A) HG)
    (Z : Scheme.{u})
    (f : FullGInvariantMorphism (A := A) (G := G) Z)
    (u : HG.Q ⟶ Z)
    (hu : HG.projection D.overlap ≫ u = f.hom) :
    u = D.factor Z f :=
  D.factor_uniq Z f u hu

/-- The actual quotient property has no additional residual beyond projection
overlap compatibility. -/
theorem actualQuotientUniversalProperty_exact
    (HC : ChartOverlapComparison (A := A) HG) :
    (Nonempty (ActualQuotientUniversalPropertyData (A := A) HG) ↔
      HG.OverlapCompatibility) := by
  constructor
  · rintro ⟨D⟩
    exact D.overlap
  · intro h
    exact actualQuotientUniversalPropertyData_exists (A := A) HG HC h

/-- Complete field agreement for the actual data. -/
theorem actualQuotientUniversalPropertyData_fields
    (HC : ChartOverlapComparison (A := A) HG)
    (hoverlap : HG.OverlapCompatibility) :
    (actualQuotientUniversalPropertyData (A := A) HG HC hoverlap).overlap = hoverlap ∧
      (∀ (Z : Scheme.{u})
        (f : FullGInvariantMorphism (A := A) (G := G) Z),
        HG.projection hoverlap ≫
            (actualQuotientUniversalPropertyData (A := A) HG HC hoverlap).factor Z f =
          f.hom) :=
  ⟨rfl, fun Z f =>
    actualQuotientUniversalPropertyData_factor_fac (A := A) HG
      (actualQuotientUniversalPropertyData (A := A) HG HC hoverlap) Z f⟩

end ActualFinalProjections

end ABCBridge.QuotientUniversalPropertyActualFinal
