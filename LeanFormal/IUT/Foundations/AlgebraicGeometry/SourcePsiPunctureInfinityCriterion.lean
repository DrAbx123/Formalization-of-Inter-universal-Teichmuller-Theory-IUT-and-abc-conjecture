import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.RingTheory.DedekindDomain.AdicValuation

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiPunctureInfinityCriterion

open LeanFormal.IUT Theorem311Source
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev SourcePunctureCurve : PuncturedEllipticCurve S.arithmetic.F :=
  S.arithmetic.curve

noncomputable abbrev SourcePunctureBaseChange :
    PuncturedEllipticCurve (v.adicCompletion S.arithmetic.F) :=
  SourcePunctureCurve S |>.baseChange (v.adicCompletion S.arithmetic.F)

noncomputable def sourcePuncturePoint :
    (SourcePunctureBaseChange S v).curve.toProjective.Point :=
  (SourcePunctureBaseChange S v).puncture

noncomputable def sourcePunctureAffineLift :
    (SourcePunctureBaseChange S v).curve.toAffine.Point :=
  (sourcePuncturePoint S v).toAffineLift

def PointClassZeqZero
    (P : WeierstrassCurve.Projective.PointClass (v.adicCompletion S.arithmetic.F)) : Prop :=
  ∃ Q : Fin 3 → v.adicCompletion S.arithmetic.F,
    P = Quotient.mk _ Q ∧ Q 2 = 0

theorem sourcePuncture_atInfinity_iff_ZeqZero :
    sourcePunctureAffineLift S v = 0 ↔
      PointClassZeqZero S v (sourcePuncturePoint S v).point := by
  classical
  let W := (SourcePunctureBaseChange S v).curve.toProjective
  constructor
  · intro hzero
    have hpoint : sourcePuncturePoint S v = 0 := by
      apply (WeierstrassCurve.Projective.Point.toAffineAddEquiv W).injective
      change sourcePunctureAffineLift S v =
        (WeierstrassCurve.Projective.Point.toAffineAddEquiv W) 0
      rw [hzero]
      exact (map_zero (WeierstrassCurve.Projective.Point.toAffineAddEquiv W)).symm
    refine ⟨![0, 1, 0], ?_, by simp⟩
    rw [hpoint, WeierstrassCurve.Projective.Point.zero_point]
  · rintro ⟨Q, hQ, hQz⟩
    let P' : (SourcePunctureBaseChange S v).curve.toProjective.Point :=
      ⟨by
        have hns := (sourcePuncturePoint S v).nonsingular
        rw [hQ] at hns
        exact hns⟩
    have hPP' : sourcePuncturePoint S v = P' := by
      apply WeierstrassCurve.Projective.Point.ext
      exact hQ
    change (sourcePuncturePoint S v).toAffineLift = 0
    rw [hPP']
    exact WeierstrassCurve.Projective.Point.toAffineLift_of_Z_eq_zero
      (W := (SourcePunctureBaseChange S v).curve.toProjective) P'.nonsingular hQz

structure SourcePsiPunctureAffineCoordinates where
  x : v.adicCompletion S.arithmetic.F
  y : v.adicCompletion S.arithmetic.F
  nonsingular : (SourcePunctureBaseChange S v).curve.toAffine.Nonsingular x y
  affine_eq : sourcePunctureAffineLift S v = Affine.Point.some x y nonsingular

theorem punctureAffineCoordinates_of_not_infinity
    (hne : ¬ sourcePunctureAffineLift S v = 0) :
    Nonempty (SourcePsiPunctureAffineCoordinates S v) := by
  cases hlift : sourcePunctureAffineLift S v with
  | zero => exact (hne hlift).elim
  | some x y ns => exact ⟨⟨x, y, ns, hlift⟩⟩

def SourcePsiPunctureCoordinateIntegral
    (x : v.adicCompletion S.arithmetic.F) : Prop :=
  ∃ x₀ : v.adicCompletionIntegers S.arithmetic.F,
    algebraMap (v.adicCompletionIntegers S.arithmetic.F)
      (v.adicCompletion S.arithmetic.F) x₀ = x

structure SourcePsiPunctureAffineIntegralData where
  x : v.adicCompletionIntegers S.arithmetic.F
  y : v.adicCompletionIntegers S.arithmetic.F
  nonsingular : (SourcePunctureBaseChange S v).curve.toAffine.Nonsingular
    (algebraMap (v.adicCompletionIntegers S.arithmetic.F)
      (v.adicCompletion S.arithmetic.F) x)
    (algebraMap (v.adicCompletionIntegers S.arithmetic.F)
      (v.adicCompletion S.arithmetic.F) y)
  affine_eq : sourcePunctureAffineLift S v =
    .some (algebraMap (v.adicCompletionIntegers S.arithmetic.F)
      (v.adicCompletion S.arithmetic.F) x)
      (algebraMap (v.adicCompletionIntegers S.arithmetic.F)
        (v.adicCompletion S.arithmetic.F) y) nonsingular

def SourcePsiPunctureTrichotomy : Prop :=
  sourcePunctureAffineLift S v = 0 ∨
    (∃ C : SourcePsiPunctureAffineCoordinates S v,
      ¬ SourcePsiPunctureCoordinateIntegral S v C.x ∨
      ¬ SourcePsiPunctureCoordinateIntegral S v C.y) ∨
    Nonempty (SourcePsiPunctureAffineIntegralData S v)

theorem sourcePsiPuncture_trichotomy :
    SourcePsiPunctureTrichotomy S v := by
  classical
  by_cases hinf : sourcePunctureAffineLift S v = 0
  · exact Or.inl hinf
  · rcases punctureAffineCoordinates_of_not_infinity S v hinf with ⟨C⟩
    by_cases hx : SourcePsiPunctureCoordinateIntegral S v C.x
    · by_cases hy : SourcePsiPunctureCoordinateIntegral S v C.y
      · obtain ⟨x₀, hx₀⟩ := hx
        obtain ⟨y₀, hy₀⟩ := hy
        refine Or.inr (Or.inr ⟨?_⟩)
        exact ⟨x₀, y₀, by simpa [hx₀, hy₀] using C.nonsingular,
          by simpa [hx₀, hy₀] using C.affine_eq⟩
      · exact Or.inr (Or.inl ⟨C, Or.inr hy⟩)
    · exact Or.inr (Or.inl ⟨C, Or.inl hx⟩)

end LeanFormal.IUT.SourcePsiPunctureInfinityCriterion
end