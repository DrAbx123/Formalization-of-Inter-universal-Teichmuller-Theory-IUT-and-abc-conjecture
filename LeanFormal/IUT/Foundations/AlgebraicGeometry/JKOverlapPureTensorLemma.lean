import Mathlib.RingTheory.Flat.Localization

noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

/-!
# Pure-tensor cancellation for the JK overlap-to-triple map

This file isolates the pure-tensor computation that the JK producer needs.
It states the result for an arbitrary `Algebra (overlapRing i j) (tripleRing i j k)`
and scalar tower, so the consumer supplies its actual localization instances.
-/

namespace ABCBridge.JKOverlapPureTensorLemma

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (t : ι → R)

/-- The chart localization. -/
abbrev chartRing (i : ι) : Type u := Localization.Away (t i)

/-- The overlap localization. -/
abbrev overlapRing (i j : ι) : Type u := Localization.Away (t i * t j)

/-- The triple localization. -/
abbrev tripleRing (i j k : ι) : Type u := Localization.Away (t i * t j * t k)

/-- The common-target `(i,j)` base map. -/
noncomputable def overlapToTripleBase (i j k : ι) :
    overlapRing (R := R) (t := t) i j →ₐ[R] tripleRing (R := R) (t := t) i j k :=
  { toRingHom := IsLocalization.Away.awayToAwayRight (t i * t j) (t k)
    commutes' := fun r => by
      change IsLocalization.Away.awayToAwayRight (t i * t j) (t k)
        (algebraMap R (overlapRing (R := R) (t := t) i j) r) =
        algebraMap R (tripleRing (R := R) (t := t) i j k) r
      exact IsLocalization.Away.awayToAwayRight_eq (t i * t j) (t k) r }

section PureTensor

variable (i j k : ι)
  [Algebra (overlapRing (R := R) (t := t) i j) (tripleRing (R := R) (t := t) i j k)]
  [IsScalarTower R (overlapRing (R := R) (t := t) i j) (tripleRing (R := R) (t := t) i j k)]

/-- `cancelBaseChange` on `includeRight` of a pure tensor. -/
theorem cancelBaseChange_includeRight_tmul
    (b : overlapRing (R := R) (t := t) i j) (a : A) :
    Algebra.TensorProduct.cancelBaseChange (R := R)
      (S := overlapRing (R := R) (t := t) i j)
      (T := tripleRing (R := R) (t := t) i j k)
      (A := tripleRing (R := R) (t := t) i j k) (B := A)
      (Algebra.TensorProduct.includeRight (b ⊗ₜ[R] a)) =
    (algebraMap (overlapRing (R := R) (t := t) i j)
        (tripleRing (R := R) (t := t) i j k) b) ⊗ₜ[R] a := by
  rw [Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.cancelBaseChange_tmul]
  simp only [Algebra.smul_def, mul_one]

/-- The exact combined cancellation identity needed by `overlapToTriple_pure`.
The `cancelBaseChange` output already lives in `tripleRing i j k ⊗[R] A`, so no
further `overlapToTripleBase` map is applied.
-/
theorem cancelBaseChange_includeRight_tmul_map
    (b : overlapRing (R := R) (t := t) i j) (a : A) :
    Algebra.TensorProduct.cancelBaseChange (R := R)
      (S := overlapRing (R := R) (t := t) i j)
      (T := tripleRing (R := R) (t := t) i j k)
      (A := tripleRing (R := R) (t := t) i j k) (B := A)
      (Algebra.TensorProduct.includeRight (b ⊗ₜ[R] a)) =
    (algebraMap (overlapRing (R := R) (t := t) i j)
      (tripleRing (R := R) (t := t) i j k) b) ⊗ₜ[R] a :=
  cancelBaseChange_includeRight_tmul (R := R) (A := A) (t := t) i j k b a

end PureTensor

end ABCBridge.JKOverlapPureTensorLemma