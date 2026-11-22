import tmp.sheaf.xif.paper.S3135ValueGroupCompatibilityActual

/-!
# task-72 (ii): model value data — CONSTRUCTIVE instance from the global realified divisor group

**Model-construction component, not a paper object.**  Bottom-up as required by the
non-circularity criterion: this file defines the model value package as DATA and
*constructs* it from the actual realified objects — no equality between a frozen
`OriginalInput` action and the model action is assumed.

`S3135ModelValueData`: a value monoid with a degree map to `Multiplicative R`, a
Real-indexed action, and the action's degree faithfulness as a FIELD (so the model
build supplies it definitionally).

`s3135_globalRealifiedModelValueData`: the actual instance —
`Mon := GlobalDivisorMonoid (X := X)`, `degree := globalDegree`,
`posRealAction := normalizedRealifiedPrimePowerHom vp`, faithfulness from the citable
`normalizedRealifiedPrimePowerHom_degree` (`globalDegree (hom r) = r`).

The next construction step (qpilot+abc joint) is the model `FPrimeStrip`/`OriginalInput`
assembly with `Mon := fun _ => S3135ModelValueData.Mon` and the model
`SourceImageRealization` whose `posRealAction` is this action *by definition*
(so F4.a's compatibility holds by construction through
`S3135ValueGroupCompatibilityActual`, no assumed equality).
-/

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeUnconditionalActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupCompatibilityActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput

namespace LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual

/-- **Model value package (DATA, constructive)**: a commutative monoid with a degree to
the multiplicative reals, a Real-indexed action, and degree faithfulness of the action. -/
structure S3135ModelValueData where
  Mon : Type
  commMonoid : CommMonoid Mon
  degree : Mon →* Multiplicative ℝ
  posRealAction : Multiplicative ℝ →* Mon
  degree_posRealAction : ∀ r : Multiplicative ℝ, degree (posRealAction r) = r

attribute [instance] S3135ModelValueData.commMonoid

/-- **The actual constructed instance**: the global realified divisor group with its
actual degree and normalized generator action. -/
noncomputable def s3135_globalRealifiedModelValueData
    {l : PrimeGeFive} (X : N8NativeInput l) (vp : GlobalPrimeIndex (X := X)) :
    S3135ModelValueData where
  Mon := GlobalDivisorMonoid (X := X)
  commMonoid := inferInstance
  degree := globalDegree (X := X)
  posRealAction := normalizedRealifiedPrimePowerHom (X := X) vp
  degree_posRealAction := normalizedRealifiedPrimePowerHom_degree (X := X) vp

/-- The degree law of the constructed model package, restated for consumers. -/
theorem s3135_globalRealifiedModelValueData_degree
    {l : PrimeGeFive} (X : N8NativeInput l) (vp : GlobalPrimeIndex (X := X))
    (r : Multiplicative ℝ) :
    (s3135_globalRealifiedModelValueData X vp).degree
        ((s3135_globalRealifiedModelValueData X vp).posRealAction r) = r :=
  (s3135_globalRealifiedModelValueData X vp).degree_posRealAction r

#check S3135ModelValueData
#check s3135_globalRealifiedModelValueData
#check s3135_globalRealifiedModelValueData_degree

end LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual
end
