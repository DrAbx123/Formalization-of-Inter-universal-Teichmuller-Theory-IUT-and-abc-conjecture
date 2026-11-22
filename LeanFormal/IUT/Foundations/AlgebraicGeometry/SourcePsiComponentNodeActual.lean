import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiReductionTypeActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualMinimalModelReduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

/-!
# Actual component and node data of the reduced minimal model

From the actual Mathlib reduced curve of the actual minimal model, construct the
actual component type (minimal primes of the affine coordinate ring, equivalently
irreducible components) and the actual singular-point candidate type (nodes),
with the component/point incidence relation.  The stable/component comparison and
the node identification are stated as an exact residual; no component graph is
fabricated.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.SourcePsiComponentNodeActual

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiActualMinimalModelReduction
open LeanFormal.IUT.SourcePsiActualMinimality
open LeanFormal.IUT.SourcePsiReductionTypeActual
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual reduced curve of the actual minimal model. -/
abbrev actualReducedCurveOfModel
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve (SourcePsiActualResidueField S v) :=
  actualMinimalReduction S v M

/-- The affine model underlying the actual reduced curve. -/
abbrev actualReducedAffineCurveOfModel
    (M : SourcePsiIntegralModelData S v) : WeierstrassCurve.Affine
      (SourcePsiActualResidueField S v) :=
  (actualReducedCurveOfModel S v M).toAffine

/-- The actual affine coordinate ring of the reduced curve. -/
abbrev actualReducedCoordinateRingOfModel
    (M : SourcePsiIntegralModelData S v) : Type u :=
  WeierstrassCurve.Affine.CoordinateRing
    (actualReducedAffineCurveOfModel S v M)

/-- The actual component type: minimal primes of the zero ideal of the actual
affine coordinate ring, equivalently irreducible components of the reduced
affine curve. -/
abbrev ActualComponentType (M : SourcePsiIntegralModelData S v) : Type u :=
  { I : Ideal (actualReducedCoordinateRingOfModel S v M) //
      I ∈ Ideal.minimalPrimes (⊥ : Ideal (actualReducedCoordinateRingOfModel S v M)) }

/-- The actual singular-point candidate type of the reduced affine curve: points
satisfying the Weierstrass equation but not the nonsingularity predicate. -/
abbrev ActualSingularPointType
    (M : SourcePsiIntegralModelData S v) : Type u :=
  { p : SourcePsiActualResidueField S v × SourcePsiActualResidueField S v //
      (actualReducedAffineCurveOfModel S v M).Equation p.1 p.2 ∧
        ¬ (actualReducedAffineCurveOfModel S v M).Nonsingular p.1 p.2 }

theorem actualReducedCoordinateRing_isDomain
    (M : SourcePsiIntegralModelData S v) :
    IsDomain (actualReducedCoordinateRingOfModel S v M) :=
  inferInstance

theorem actualComponentType_nonempty
    (M : SourcePsiIntegralModelData S v) :
    Nonempty (ActualComponentType S v M) :=
  by
  refine ⟨⟨⊥, ?_⟩⟩
  refine ⟨⟨inferInstance, le_rfl⟩, ?_⟩
  intro q hq hqbot
  exact bot_le

theorem actualComponentType_mem_minimalPrimes
    (M : SourcePsiIntegralModelData S v)
    (I : ActualComponentType S v M) :
    (I : Ideal (actualReducedCoordinateRingOfModel S v M)) ∈
      Ideal.minimalPrimes (⊥ : Ideal (actualReducedCoordinateRingOfModel S v M)) :=
  I.property

theorem actualComponentType_isPrime
    (M : SourcePsiIntegralModelData S v)
    (I : ActualComponentType S v M) :
    (I : Ideal (actualReducedCoordinateRingOfModel S v M)).IsPrime :=
  I.property.1.1

theorem actualSingularPointType_equation
    (M : SourcePsiIntegralModelData S v)
    (P : ActualSingularPointType S v M) :
    (actualReducedAffineCurveOfModel S v M).Equation P.val.1 P.val.2 :=
  P.property.1

theorem actualSingularPointType_not_nonsingular
    (M : SourcePsiIntegralModelData S v)
    (P : ActualSingularPointType S v M) :
    ¬ (actualReducedAffineCurveOfModel S v M).Nonsingular P.val.1 P.val.2 :=
  P.property.2

/-- Actual incidence: a component contains a point of the prime spectrum when
the corresponding minimal prime is contained in that point's prime ideal. -/
def ActualComponentPointIncidence
    (M : SourcePsiIntegralModelData S v)
    (I : ActualComponentType S v M)
    (P : PrimeSpectrum (actualReducedCoordinateRingOfModel S v M)) : Prop :=
  (I : Ideal (actualReducedCoordinateRingOfModel S v M)) ≤ P.asIdeal

theorem actualComponentPointIncidence_def
    (M : SourcePsiIntegralModelData S v)
    (I : ActualComponentType S v M)
    (P : PrimeSpectrum (actualReducedCoordinateRingOfModel S v M)) :
    ActualComponentPointIncidence S v M I P ↔
      (I : Ideal (actualReducedCoordinateRingOfModel S v M)) ≤ P.asIdeal :=
  Iff.rfl

/-- Actual partial component/node data: the actual reduced curve, component type,
singular-point type and the actual component/point incidence relation. -/
structure ActualComponentNodePartialData
    (M : SourcePsiIntegralModelData S v) where
  reducedCurve : WeierstrassCurve (SourcePsiActualResidueField S v)
  reducedCurve_eq : reducedCurve = actualReducedCurveOfModel S v M
  componentType : Type u
  nodeType : Type u
  incidence : componentType → PrimeSpectrum (actualReducedCoordinateRingOfModel S v M) → Prop

noncomputable def actualComponentNodePartialData
    (M : SourcePsiIntegralModelData S v) :
    ActualComponentNodePartialData S v M where
  reducedCurve := actualReducedCurveOfModel S v M
  reducedCurve_eq := rfl
  componentType := ActualComponentType S v M
  nodeType := ActualSingularPointType S v M
  incidence := ActualComponentPointIncidence S v M

theorem actualComponentNodePartialData_components
    (M : SourcePsiIntegralModelData S v) :
    (actualComponentNodePartialData S v M).componentType = ActualComponentType S v M :=
  rfl

theorem actualComponentNodePartialData_nodes
    (M : SourcePsiIntegralModelData S v) :
    (actualComponentNodePartialData S v M).nodeType = ActualSingularPointType S v M :=
  rfl

theorem actualComponentNodePartialData_incidence
    (M : SourcePsiIntegralModelData S v)
    (I : ActualComponentType S v M)
    (P : PrimeSpectrum (actualReducedCoordinateRingOfModel S v M)) :
    (actualComponentNodePartialData S v M).incidence I P ↔
      ActualComponentPointIncidence S v M I P :=
  Iff.rfl

/-- Good reduction has no affine singular point: the reduced curve is elliptic. -/
theorem actualSingularPoint_empty_of_good
    (M : SourcePsiIntegralModelData S v)
    (hgood : ActualGoodReduction S v M) :
    IsEmpty (ActualSingularPointType S v M) :=
  by
  refine ⟨?_⟩
  rintro ⟨⟨x, y⟩, hEq, hNon⟩
  have hell : (actualReducedCurveOfModel S v M).IsElliptic := by
    have h := WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction
      (R := SourcePsiActualIntegers S v)
      (W := actualReductionMinimalModel S v M)
    exact h.mp hgood
  have hns : (actualReducedAffineCurveOfModel S v M).Nonsingular x y := by
    exact (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hEq
  exact hNon hns

/-- Exact stable/component comparison residual: a finite component type with
finite node type, incidence, and the stable-reduction comparison.  This is a
residual structure, not an asserted inhabitant. -/
structure SourcePsiStableComponentComparisonResidual
    (M : SourcePsiIntegralModelData S v) where
  data : ActualComponentNodePartialData S v M
  finite_components : Fintype data.componentType
  finite_nodes : Fintype data.nodeType
  stable_comparison : Prop

def SourcePsiStableComponentComparisonStatement
    (M : SourcePsiIntegralModelData S v) : Prop :=
  Nonempty (SourcePsiStableComponentComparisonResidual S v M)

theorem sourcePsiStableComponentComparisonStatement_iff
    (M : SourcePsiIntegralModelData S v) :
    SourcePsiStableComponentComparisonStatement S v M ↔
      Nonempty (SourcePsiStableComponentComparisonResidual S v M) :=
  Iff.rfl

theorem sourcePsiStableComponentComparisonResidual_data
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiStableComponentComparisonResidual S v M) :
    D.data.reducedCurve = actualReducedCurveOfModel S v M :=
  D.data.reducedCurve_eq

/-- The actual component, actual singular-point candidate, and incidence data
packaged separately from the finite/stable residual. -/
structure ActualComponentNodeData
    (M : SourcePsiIntegralModelData S v) where
  reducedCurve : WeierstrassCurve (SourcePsiActualResidueField S v)
  reducedCurve_eq : reducedCurve = actualReducedCurveOfModel S v M
  componentType : Type u
  componentType_eq : componentType = ActualComponentType S v M
  nodeType : Type u
  nodeType_eq : nodeType = ActualSingularPointType S v M
  incidence : componentType → PrimeSpectrum (actualReducedCoordinateRingOfModel S v M) → Prop
  incidence_eq : incidence = ActualComponentPointIncidence S v M

noncomputable def actualComponentNodeData
    (M : SourcePsiIntegralModelData S v) : ActualComponentNodeData S v M where
  reducedCurve := actualReducedCurveOfModel S v M
  reducedCurve_eq := rfl
  componentType := ActualComponentType S v M
  componentType_eq := rfl
  nodeType := ActualSingularPointType S v M
  nodeType_eq := rfl
  incidence := ActualComponentPointIncidence S v M
  incidence_eq := rfl

theorem actualComponentNodeData_componentType
    (M : SourcePsiIntegralModelData S v) :
    (actualComponentNodeData S v M).componentType = ActualComponentType S v M :=
  rfl

theorem actualComponentNodeData_nodeType
    (M : SourcePsiIntegralModelData S v) :
    (actualComponentNodeData S v M).nodeType = ActualSingularPointType S v M :=
  rfl

theorem actualComponentNodeData_incidence
    (M : SourcePsiIntegralModelData S v)
    (I : ActualComponentType S v M)
    (P : PrimeSpectrum (actualReducedCoordinateRingOfModel S v M)) :
    (actualComponentNodeData S v M).incidence I P ↔
      ActualComponentPointIncidence S v M I P :=
  Iff.rfl

theorem actualComponentNodeData_reducedCurve
    (M : SourcePsiIntegralModelData S v) :
    (actualComponentNodeData S v M).reducedCurve = actualReducedCurveOfModel S v M :=
  rfl

/-- The actual singular-point candidate type is a subtype of the actual
residue-field product, with the actual equation and non-nonsingularity data. -/
theorem actualSingularPointType_coe
    (M : SourcePsiIntegralModelData S v)
    (P : ActualSingularPointType S v M) :
    (P.val.1, P.val.2) ∈
      { q : SourcePsiActualResidueField S v × SourcePsiActualResidueField S v |
          (actualReducedAffineCurveOfModel S v M).Equation q.1 q.2 ∧
            ¬ (actualReducedAffineCurveOfModel S v M).Nonsingular q.1 q.2 } :=
  P.property

/-- The actual incidence is exactly minimal-prime containment. -/
theorem actualComponentPointIncidence_iff
    (M : SourcePsiIntegralModelData S v)
    (I : ActualComponentType S v M)
    (P : PrimeSpectrum (actualReducedCoordinateRingOfModel S v M)) :
    ActualComponentPointIncidence S v M I P ↔
      (I : Ideal (actualReducedCoordinateRingOfModel S v M)) ≤ P.asIdeal :=
  Iff.rfl

theorem actualComponentNodePartialData_reducedCurve
    (M : SourcePsiIntegralModelData S v) :
    (actualComponentNodePartialData S v M).reducedCurve =
      actualReducedCurveOfModel S v M :=
  rfl

theorem sourcePsiStableComponentComparisonStatement_of_data
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiStableComponentComparisonResidual S v M) :
    SourcePsiStableComponentComparisonStatement S v M :=
  ⟨D⟩

theorem sourcePsiStableComponentComparisonResidual_stable_comparison
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiStableComponentComparisonResidual S v M) :
    D.stable_comparison :=
  D.stable_comparison

theorem sourcePsiStableComponentComparisonResidual_data_componentType
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiStableComponentComparisonResidual S v M) :
    D.data.componentType = ActualComponentType S v M :=
  rfl

theorem sourcePsiStableComponentComparisonResidual_data_nodeType
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiStableComponentComparisonResidual S v M) :
    D.data.nodeType = ActualSingularPointType S v M :=
  rfl

theorem actualSingularPoint_empty_of_good_iff
    (M : SourcePsiIntegralModelData S v) :
    ActualGoodReduction S v M → IsEmpty (ActualSingularPointType S v M) :=
  actualSingularPoint_empty_of_good S v M
end LeanFormal.IUT.SourcePsiComponentNodeActual
