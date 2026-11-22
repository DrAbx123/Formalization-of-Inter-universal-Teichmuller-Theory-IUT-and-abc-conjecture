/-
  The unit map induced by an actual evaluation/retraction is split surjective.

  Given `E : SourcePsiIntegralEvaluationData`, the unit map

    (integral coordinate ring)^× -> (v.adicCompletionIntegers)^×

  retracts the actual constant-unit inclusion.  Hence it is surjective, its
  kernel is an actual subgroup, and the quotient by the kernel is canonically
  isomorphic to the completion integer units.  The kernel meets the constant-unit
  subgroup trivially.  No evaluation datum is constructed here.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiEvaluationObstruction

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiIntegralUnitMapSurjectivity

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelUnitMapExistence
open LeanFormal.IUT.SourcePsiEvaluationObstruction

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))
  (h : SourcePsiCoefficientsIntegral S v)

/-- The actual unit map induced by an evaluation/retraction. -/
abbrev SourcePsiIntegralUnitMap (E : SourcePsiIntegralEvaluationData S v h) :
    SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h →*
      (SourcePsiCompletionIntegers S v)ˣ :=
  E.toBaseUnits

/-- The constant-unit inclusion is a section of the unit map. -/
theorem sourcePsiIntegralConstantUnits_section
    (E : SourcePsiIntegralEvaluationData S v h) :
    (SourcePsiIntegralUnitMap S v h E).comp
        (sourcePsiIntegralConstantUnits S v h) =
      MonoidHom.id ((SourcePsiCompletionIntegers S v)ˣ) := by
  ext r
  exact E.toBaseUnits_constant r

/-- The unit map is surjective. -/
theorem SourcePsiIntegralUnitMap_surjective
    (E : SourcePsiIntegralEvaluationData S v h) :
    Function.Surjective (SourcePsiIntegralUnitMap S v h E) := by
  intro r
  refine ⟨sourcePsiIntegralConstantUnits S v h r, ?_⟩
  exact E.toBaseUnits_constant r

/-- The constant-unit inclusion is injective. -/
theorem sourcePsiIntegralConstantUnits_injective
    (E : SourcePsiIntegralEvaluationData S v h) :
    Function.Injective (sourcePsiIntegralConstantUnits S v h) := by
  intro r s hrs
  apply_fun (SourcePsiIntegralUnitMap S v h E) at hrs
  simpa [E.toBaseUnits_constant] using hrs

/-- The actual kernel of the unit map. -/
noncomputable def SourcePsiIntegralUnitMapKernel
    (E : SourcePsiIntegralEvaluationData S v h) :
    Subgroup (SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h) :=
  (SourcePsiIntegralUnitMap S v h E).ker

theorem mem_SourcePsiIntegralUnitMapKernel_iff
    (E : SourcePsiIntegralEvaluationData S v h)
    (x : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h) :
    x ∈ SourcePsiIntegralUnitMapKernel S v h E ↔
      SourcePsiIntegralUnitMap S v h E x = 1 :=
  Iff.rfl

/-- The kernel of the unit map meets the constant-unit subgroup trivially. -/
theorem SourcePsiIntegralUnitMapKernel_inf_constants_bot
    (E : SourcePsiIntegralEvaluationData S v h) :
    SourcePsiIntegralUnitMapKernel S v h E ⊓
        (sourcePsiIntegralConstantUnits S v h).range = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxker, hxrange⟩ := hx
  obtain ⟨r, rfl⟩ := hxrange
  have hval : SourcePsiIntegralUnitMap S v h E
      (sourcePsiIntegralConstantUnits S v h r) = 1 := hxker
  rw [E.toBaseUnits_constant] at hval
  subst hval
  exact Subgroup.mem_bot.mpr rfl

/-- The quotient by the unit-map kernel is the actual completion integer unit
group. -/
noncomputable def SourcePsiIntegralUnitMapQuotientEquiv
    (E : SourcePsiIntegralEvaluationData S v h) :
    (SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h ⧸
        SourcePsiIntegralUnitMapKernel S v h E) ≃*
      (SourcePsiCompletionIntegers S v)ˣ :=
  MonoidHom.quotientKerEquivOfSurjective
    (SourcePsiIntegralUnitMap S v h E)
    (SourcePsiIntegralUnitMap_surjective S v h E)

theorem SourcePsiIntegralUnitMapQuotientEquiv_mk
    (E : SourcePsiIntegralEvaluationData S v h)
    (x : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h) :
    SourcePsiIntegralUnitMapQuotientEquiv S v h E (QuotientGroup.mk x) =
      SourcePsiIntegralUnitMap S v h E x := rfl

/-! ## Exact consequences and residual

Under an actual evaluation/retraction datum:
* the unit map is split surjective;
* the constant-unit inclusion is a section;
* the kernel is an actual subgroup and its quotient is the completion integer
  unit group;
* the kernel meets the constants trivially.

NOT constructed:
1. the evaluation/retraction datum itself (see the point/obstruction file);
2. a proof that the kernel is trivial or that the unit map is injective;
3. a description of the kernel beyond the retraction/constant splitting;
4. any identification of the integral coordinate ring units with the source
  Psi^cns integral units.

No evaluation datum, integral point, or separated unit is fabricated by this
file.  The statements are conditional on an explicit `E`.
-/

end LeanFormal.IUT.SourcePsiIntegralUnitMapSurjectivity

end
