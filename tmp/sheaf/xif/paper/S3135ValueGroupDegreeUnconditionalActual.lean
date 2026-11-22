import tmp.sheaf.xif.paper.S3133ValueGroupDegreeActual
import tmp.sheaf.xif.paper.S3133GlobalPrimeWeightActual

/-!
# task-44 (3): the normalized Real-indexed degree action is now UNCONDITIONAL

**COMPONENT, not a paper object.**  Consumer: task-39 value-group identification
(future: paper value-group degree splitting, IUT II Example 1.8(ix)).

Task-33 constructed the normalized Real-indexed generator action on the actual
realified divisor group assuming a nonzero arithmetic weight
(`globalPrimeWeight v ≠ 0`).  qpilot's citable `S3133GlobalPrimeWeightActual`
supplies `globalPrimeWeight_ne_zero (v)` for every actual global prime index, so the
hypothesis can be dropped: the actual Real-indexed degree-faithful monoid action

`normalizedRealifiedPrimePowerHom v r = [v]^(r / globalPrimeWeight v)`,
`globalDegree (normalizedRealifiedPrimePowerHom v r) = r`

exists for EVERY actual global prime index `v`, with no side condition.  This
removes the last hypothesis from the F4 (a) value-group side; the remaining F4 (a)
datum is the source-monoid identification
`S3135ValueMonoidIdentification` (task-39).
-/

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual
open LeanFormal.IUT.XiFPaper.S3133GlobalPrimeWeightActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput

namespace LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeUnconditionalActual

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The normalization hom `r |-> r / w` on the multiplicative reals. -/
noncomputable def realDivNormalizationHom
    (w : ℝ) : Multiplicative ℝ →* Multiplicative ℝ where
  toFun r := Multiplicative.ofAdd (r.toAdd / w)
  map_one' := by
    show Multiplicative.ofAdd ((1 : Multiplicative ℝ).toAdd / w) = 1
    simp
  map_mul' := by
    intro a b
    show Multiplicative.ofAdd ((a * b).toAdd / w) =
      Multiplicative.ofAdd (a.toAdd / w) * Multiplicative.ofAdd (b.toAdd / w)
    have h : (a * b).toAdd = a.toAdd + b.toAdd := rfl
    have hR : Multiplicative.ofAdd (a.toAdd / w) * Multiplicative.ofAdd (b.toAdd / w) =
        Multiplicative.ofAdd (a.toAdd / w + b.toAdd / w) := rfl
    rw [hR, h, add_div]

/-- The **unconditional** normalized Real-indexed generator action on the actual
realified divisor group, for every actual global prime index. -/
noncomputable def normalizedRealifiedPrimePowerHom
    (v : GlobalPrimeIndex (X := X)) :
    Multiplicative ℝ →* GlobalDivisorMonoid (X := X) :=
  (globalRealifiedPrimePowerHom (X := X) v).comp
    (realDivNormalizationHom (globalPrimeWeight (X := X) v))

/-- **Unconditional degree faithfulness** of the actual value-group action. -/
theorem normalizedRealifiedPrimePowerHom_degree
    (v : GlobalPrimeIndex (X := X)) (r : Multiplicative ℝ) :
    globalDegree (X := X) (normalizedRealifiedPrimePowerHom (X := X) v r) = r := by
  unfold normalizedRealifiedPrimePowerHom realDivNormalizationHom
  simp only [MonoidHom.comp_apply]
  rw [globalDegree_comp_primePowerHom]
  change Multiplicative.ofAdd
    (r.toAdd / globalPrimeWeight (X := X) v * globalPrimeWeight (X := X) v) = r
  rw [div_mul_cancel₀ _ (globalPrimeWeight_ne_zero (X := X) v)]
  simp

/-- The unconditional actual Real-indexed degree-faithful action, packaged. -/
def S3135UnconditionalRealifiedDegreeSection
    (v : GlobalPrimeIndex (X := X)) : Prop :=
  ∀ r : Multiplicative ℝ,
    globalDegree (X := X) (normalizedRealifiedPrimePowerHom (X := X) v r) = r

theorem s3135_unconditionalRealifiedDegreeSection
    (v : GlobalPrimeIndex (X := X)) :
    S3135UnconditionalRealifiedDegreeSection (X := X) v :=
  fun r => normalizedRealifiedPrimePowerHom_degree (X := X) v r

#check normalizedRealifiedPrimePowerHom
#check normalizedRealifiedPrimePowerHom_degree
#check s3135_unconditionalRealifiedDegreeSection

end LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeUnconditionalActual
end
