import LeanFormal.IUT.Foundations.LocalFields.AlgebraicUnitLogarithm
import LeanFormal.IUT.Foundations.LocalFields.AlgebraicUnitPairCarrier
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmGalois

/-!
# The actual algebraic-unit logarithm homomorphism

A common finite complete carrier proves multiplication. Evaluation in
any finite presentation also proves naturality, including the actual
Galois action on the ambient algebraic extension.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {Ω : Type*} [NormedField Ω] [IsUltrametricDist Ω]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] Ω]
variable [Algebra.IsAlgebraic ℚ_[p] Ω]

omit [Algebra.IsAlgebraic ℚ_[p] Ω] in
theorem integralUnitLiftToIntermediateField_map (F : IntermediateField ℚ_[p] Ω)
    (u : (Integers Ω)ˣ) (hu : (u.val : Ω) ∈ F) :
    integralUnitMap F.val.toRingHom (isometry_intermediateField_inclusion F)
      (integralUnitLiftToIntermediateField F u hu) = u := by
  apply Units.ext
  apply Subtype.ext
  rfl

theorem algebraicUnitLog_one : algebraicUnitLog (p := p) (1 : (Integers Ω)ˣ) = 0 := by
  let F := finiteUnitField (p := p) (1 : (Integers Ω)ˣ)
  have hu : integralUnitMap F.val.toRingHom (isometry_intermediateField_inclusion F) 1 = 1 :=
    map_one _
  rw [← hu, algebraicUnitLog_eq_map (p := p), unitLog_one (p := p), map_zero]

theorem algebraicUnitLog_mul (u v : (Integers Ω)ˣ) :
    algebraicUnitLog (p := p) (u * v) =
      algebraicUnitLog (p := p) u + algebraicUnitLog (p := p) v := by
  let F := finiteUnitPairField (p := p) u v
  let a := integralUnitLiftToIntermediateField F u (mem_finiteUnitPairField_left u v)
  let b := integralUnitLiftToIntermediateField F v (mem_finiteUnitPairField_right u v)
  let hF := isometry_intermediateField_inclusion F
  have ha : integralUnitMap F.val.toRingHom hF a = u :=
    integralUnitLiftToIntermediateField_map F u _
  have hb : integralUnitMap F.val.toRingHom hF b = v :=
    integralUnitLiftToIntermediateField_map F v _
  calc
    _ = algebraicUnitLog (p := p) (integralUnitMap F.val.toRingHom hF (a * b)) := by
      rw [map_mul, ha, hb]
    _ = F.val.toRingHom (unitLog (a * b)) :=
      algebraicUnitLog_eq_map (p := p) F.val.toRingHom hF _
    _ = F.val.toRingHom (unitLog a) + F.val.toRingHom (unitLog b) := by
      rw [unitLog_mul (p := p), map_add]
    _ = _ := by
      rw [← algebraicUnitLog_eq_map (p := p) F.val.toRingHom hF a,
        ← algebraicUnitLog_eq_map (p := p) F.val.toRingHom hF b, ha, hb]

def algebraicUnitLogHom : (Integers Ω)ˣ →* Multiplicative Ω where
  toFun u := Multiplicative.ofAdd (algebraicUnitLog (p := p) u)
  map_one' := by
    change algebraicUnitLog (Ω := Ω) (p := p) 1 = 0
    exact algebraicUnitLog_one
  map_mul' u v := by
    change algebraicUnitLog (p := p) (u * v) = _
    exact algebraicUnitLog_mul u v

theorem algebraicUnitLog_pow (u : (Integers Ω)ˣ) (n : ℕ) :
    algebraicUnitLog (p := p) (u ^ n) = n • algebraicUnitLog (p := p) u :=
  congrArg Multiplicative.toAdd ((algebraicUnitLogHom (Ω := Ω) (p := p)).map_pow u n)

theorem algebraicUnitLog_inv (u : (Integers Ω)ˣ) :
    algebraicUnitLog (p := p) u⁻¹ = -algebraicUnitLog (p := p) u :=
  congrArg Multiplicative.toAdd ((algebraicUnitLogHom (Ω := Ω) (p := p)).map_inv u)

theorem algebraicUnitLog_map
    {Λ : Type*} [NormedField Λ] [IsUltrametricDist Λ]
    [NormedAlgebra ℚ_[p] Λ] [Algebra.IsAlgebraic ℚ_[p] Λ]
    (e : Ω →+* Λ) (he : Isometry e) (u : (Integers Ω)ˣ) :
    algebraicUnitLog (p := p) (integralUnitMap e he u) = e (algebraicUnitLog (p := p) u) := by
  let F := finiteUnitField (p := p) u
  let v := finiteUnitLift (p := p) u
  let hF := isometry_intermediateField_inclusion F
  have hunit : integralUnitMap (e.comp F.val.toRingHom) (he.comp hF) v =
      integralUnitMap e he u := by
    rw [← finiteUnitLift_map (p := p) u]
    apply Units.ext
    apply Subtype.ext
    rfl
  rw [← hunit, algebraicUnitLog_eq_map (p := p) (e.comp F.val.toRingHom) (he.comp hF) v]
  rfl

theorem algebraicUnitLog_localGalois_smul
    (σ : Ω ≃ₐ[ℚ_[p]] Ω) (u : (Integers Ω)ˣ) :
    algebraicUnitLog (p := p) (σ • u) = σ (algebraicUnitLog (p := p) u) :=
  algebraicUnitLog_map σ.toRingHom (isometry_localGalois σ) u

theorem algebraicUnitLogHom_ker_eq_torsion :
    (algebraicUnitLogHom (Ω := Ω) (p := p)).ker = CommGroup.torsion (Integers Ω)ˣ := by
  ext u
  exact algebraicUnitLog_eq_zero_iff_isOfFinOrder u

end

end LeanFormal.IUT.LocalFieldLogarithm
