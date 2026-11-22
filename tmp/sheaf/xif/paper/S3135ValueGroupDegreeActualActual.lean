import tmp.sheaf.xif.paper.S3133ValueGroupDegreeActual
import tmp.sheaf.xif.paper.S3135ResidualNarrowingActual

/-!
# task-33 (a): the actual Real-indexed degree-faithful value-group action (component)

**COMPONENT, not a paper object.**  Named consumer: the task-33 F4 residual (a)
`S3135ValueGroupDegreeSection` on the actual value group; future consumer: the
paper-level value-group/degree splitting of IUT II Example 1.8(ix).

Using qpilot's actual realified global divisor group of `C^boxplus_mod`
(`S3133ValueGroupDegreeActual`, citable EXIT=0):
`globalRealifiedPrimePowerHom v : Multiplicative Real ->* GlobalDivisorMonoid` with
`globalDegree ([v]^r) = ofAdd (r * globalPrimeWeight v)`, we construct the
**normalized** Real-indexed generator action

`normalizedRealifiedPrimePowerHom v hweight r = [v]^(r / globalPrimeWeight v)`

and prove its degree is the **identity**:

`globalDegree (normalizedRealifiedPrimePowerHom v hweight r) = r`.

This is the actual degree-faithful Real-indexed action on the actual realified
divisor group (the value-group/degree-lattice side), satisfying the value-group
half of the log-shell construction on ACTUAL objects (IUT II Example 1.8(ix),
iut2.txt:2402-2409; [AbsTopIII] Proposition 5.8(ii); Remark 3.9.4; IUT III
Proposition 3.9(i) p.115).  It is NOT an arbitrary carrier: the monoid is the actual
realified divisor group of the actual Frobenioid.

Remaining exact missing (narrowed): an identification of the source value monoid
action `R.posRealAction` with this actual realified divisor action, i.e. a
degree-commuting monoid hom from `GlobalDivisorMonoid` to `Mon v` whose composite
with the normalized generator action is `R.posRealAction` (paper: the identification
of the value group of the global realified Frobenioid with the value monoid of the
prime-strip, IUT II section 1; Remark 3.9.4).  Once that identification is supplied,
`S3135ValueGroupDegreeSection` follows (task-33 (a) then closes).  Hull's additive
principal-unit log image is not involved (degree 0, cannot supply this).
-/

noncomputable section

open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeActualActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput

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

/-- The **normalized** Real-indexed generator action on the actual realified divisor
group: `r |-> [v]^(r / w)` for a global prime `v` of nonzero arithmetic weight
`w`. -/
noncomputable def normalizedRealifiedPrimePowerHom
    (v : GlobalPrimeIndex (X := X)) (hweight : globalPrimeWeight (X := X) v ≠ 0) :
    Multiplicative ℝ →* GlobalDivisorMonoid (X := X) :=
  (globalRealifiedPrimePowerHom (X := X) v).comp
    (realDivNormalizationHom (globalPrimeWeight (X := X) v))

/-- **The actual degree-faithful value-group action**: the normalized generator
action has degree the identity on the actual realified divisor group. -/
theorem normalizedRealifiedPrimePowerHom_degree
    (v : GlobalPrimeIndex (X := X)) (hweight : globalPrimeWeight (X := X) v ≠ 0)
    (r : Multiplicative ℝ) :
    globalDegree (X := X) (normalizedRealifiedPrimePowerHom (X := X) v hweight r) = r := by
  unfold normalizedRealifiedPrimePowerHom realDivNormalizationHom
  simp only [MonoidHom.comp_apply]
  rw [globalDegree_comp_primePowerHom]
  change Multiplicative.ofAdd
    (r.toAdd / globalPrimeWeight (X := X) v * globalPrimeWeight (X := X) v) = r
  rw [div_mul_cancel₀ _ hweight]
  simp

/-- The actual Real-indexed degree-faithful action, packaged. -/
def S3135RealifiedDegreeSection
    (v : GlobalPrimeIndex (X := X)) (hweight : globalPrimeWeight (X := X) v ≠ 0) : Prop :=
  ∀ r : Multiplicative ℝ,
    globalDegree (X := X) (normalizedRealifiedPrimePowerHom (X := X) v hweight r) = r

/-- The packaged section holds on the actual objects. -/
theorem s3135_realifiedDegreeSection
    (v : GlobalPrimeIndex (X := X)) (hweight : globalPrimeWeight (X := X) v ≠ 0) :
    S3135RealifiedDegreeSection (X := X) v hweight :=
  fun r => normalizedRealifiedPrimePowerHom_degree (X := X) v hweight r

#check normalizedRealifiedPrimePowerHom
#check normalizedRealifiedPrimePowerHom_degree
#check s3135_realifiedDegreeSection

end LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeActualActual
end
