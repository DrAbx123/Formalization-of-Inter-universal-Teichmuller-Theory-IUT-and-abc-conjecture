import Mathlib.RingTheory.Flat.Localization
import LeanFormal.IUT.Foundations.AlgebraicGeometry.JKOverlapPureTensorLemma

noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct

/-!
# Chart-gluing base/coefficient identity on localization generators

This bounded file proves the base-level identity needed by the chart-gluing
consumer: on a generator `algebraMap R (chartRing i) r` and a coefficient `b`, the
`(i,j)` and `(i,k)` chart-to-triple base composites agree.
-/
namespace ABCBridge.ChartGluingBaseCoefficientIdentity

universe u
variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (t : ι → R)

abbrev chartRing (i : ι) : Type u := Localization.Away (t i)
abbrev overlapRing (i j : ι) : Type u := Localization.Away (t i * t j)
abbrev tripleRing (i j k : ι) : Type u := Localization.Away (t i * t j * t k)

noncomputable def awayChartOverlap (i j : ι) :
    chartRing (R := R) (t := t) i →ₐ[R] overlapRing (R := R) (t := t) i j :=
  { toRingHom := IsLocalization.Away.awayToAwayRight (t i) (t j)
    commutes' := fun r => by
      change IsLocalization.Away.awayToAwayRight (t i) (t j)
        (algebraMap R (chartRing (R := R) (t := t) i) r) =
        algebraMap R (overlapRing (R := R) (t := t) i j) r
      exact IsLocalization.Away.awayToAwayRight_eq (t i) (t j) r }

noncomputable def baseIJ (i j k : ι) :
    overlapRing (R := R) (t := t) i j →ₐ[R] tripleRing (R := R) (t := t) i j k :=
  { toRingHom := IsLocalization.Away.awayToAwayRight (t i * t j) (t k)
    commutes' := fun r => by
      change IsLocalization.Away.awayToAwayRight (t i * t j) (t k)
        (algebraMap R (overlapRing (R := R) (t := t) i j) r) =
        algebraMap R (tripleRing (R := R) (t := t) i j k) r
      exact IsLocalization.Away.awayToAwayRight_eq (t i * t j) (t k) r }

noncomputable def baseIK (i j k : ι) :
    overlapRing (R := R) (t := t) i k →ₐ[R] tripleRing (R := R) (t := t) i j k :=
  { toRingHom := Localization.awayLift
      (algebraMap R (tripleRing (R := R) (t := t) i j k)) (t i * t k)
      (by
        have hprod : IsUnit (algebraMap R (tripleRing (R := R) (t := t) i j k)
            (t i * t j * t k)) :=
          IsLocalization.Away.algebraMap_isUnit (t i * t j * t k)
        exact isUnit_of_dvd_unit
          ⟨algebraMap R (tripleRing (R := R) (t := t) i j k) (t j), by
            rw [← map_mul]; congr 1; ring⟩ hprod)
    commutes' := fun r => by
      change Localization.awayLift (algebraMap R (tripleRing (R := R) (t := t) i j k))
        (t i * t k) _ (algebraMap R (overlapRing (R := R) (t := t) i k) r) =
        algebraMap R (tripleRing (R := R) (t := t) i j k) r
      exact IsLocalization.Away.lift_eq _ _ r }

theorem baseIJ_generator (i j k : ι) (r : R) :
    baseIJ (R := R) (t := t) i j k
        (awayChartOverlap (R := R) (t := t) i j (algebraMap R (chartRing (R := R) (t := t) i) r)) =
      algebraMap R (tripleRing (R := R) (t := t) i j k) r := by
  change baseIJ (R := R) (t := t) i j k
    (IsLocalization.Away.awayToAwayRight (t i) (t j)
      (algebraMap R (chartRing (R := R) (t := t) i) r)) =
    algebraMap R (tripleRing (R := R) (t := t) i j k) r
  rw [IsLocalization.Away.awayToAwayRight_eq]
  exact (baseIJ (R := R) (t := t) i j k).commutes r

theorem baseIK_generator (i j k : ι) (r : R) :
    baseIK (R := R) (t := t) i j k
        (awayChartOverlap (R := R) (t := t) i k (algebraMap R (chartRing (R := R) (t := t) i) r)) =
      algebraMap R (tripleRing (R := R) (t := t) i j k) r := by
  change baseIK (R := R) (t := t) i j k
    (IsLocalization.Away.awayToAwayRight (t i) (t k)
      (algebraMap R (chartRing (R := R) (t := t) i) r)) =
    algebraMap R (tripleRing (R := R) (t := t) i j k) r
  rw [IsLocalization.Away.awayToAwayRight_eq]
  exact (baseIK (R := R) (t := t) i j k).commutes r

theorem chartBaseCoefficient_generator (i j k : ι) (r : R)
    (b : FixedPoints.subalgebra R A G) :
    Algebra.TensorProduct.map (baseIJ (R := R) (t := t) i j k)
        (FixedPoints.subalgebra R A G).val
        (((awayChartOverlap (R := R) (t := t) i j)
          (algebraMap R (chartRing (R := R) (t := t) i) r)) ⊗ₜ[R] b) =
      Algebra.TensorProduct.map (baseIK (R := R) (t := t) i j k)
        (FixedPoints.subalgebra R A G).val
        (((awayChartOverlap (R := R) (t := t) i k)
          (algebraMap R (chartRing (R := R) (t := t) i) r)) ⊗ₜ[R] b) := by
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  rw [baseIJ_generator, baseIK_generator]

end ABCBridge.ChartGluingBaseCoefficientIdentity