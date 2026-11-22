import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual

/-!
# task-54/56 (1) pushforward half: multiplication-by-c is an additive Haar automorphism

**COMPONENT, not a paper object.**  Consumer: F4 (b1) `S3135AdditiveHaarModulusLaw`.

For `c ≠ 0` the map `x |-> c * x` is a continuous additive automorphism of the actual
concrete completion `concreteLogShellField`, and the pushforward of hull's actual
`sourceHullHaar` is again an additive Haar measure (Mathlib
`AddEquiv.isAddHaarMeasure_map`).  This is the pushforward half of the modulus law.

The remaining equality `mu' = C • mu` is recorded as the exact missing
`S3135HaarUniquenessScalarStep`.  Route (from Mathlib
`MeasureTheory/Measure/Haar/Unique.lean`, read 2026-11-10):
`integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport` (line 292, additive version
of `integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`) plus `Measure.ext` on
compactly-supported test functions.  CAUTION (recorded): the lemma
`Measure.addHaarScalarFactor_smul` (line 323) is the scalar-factor-under-scalar-
multiplication lemma, NOT the uniqueness equation.
Source: IUT III Proposition 3.9(i) p.115; Remark 3.9.5(i) pp.158-159.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual

namespace LeanFormal.IUT.XiFPaper.S3135HaarPushforwardActual

local instance measCSF5 : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF5 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- Multiplication by `c ≠ 0` as a continuous additive automorphism. -/
noncomputable def mulAddEquiv (c : concreteLogShellField) (hc : c ≠ 0) :
    concreteLogShellField ≃+ concreteLogShellField where
  toFun x := c * x
  invFun x := c⁻¹ * x
  left_inv x := by
    show c⁻¹ * (c * x) = x
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  right_inv x := by
    show c * (c⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  map_add' x y := by
    show c * (x + y) = c * x + c * y
    rw [mul_add]

/-- **Pushforward of the actual Haar measure under multiplication by `c ≠ 0` is again
an additive Haar measure.** -/
theorem s3135_pushforward_isAddHaar (c : concreteLogShellField) (hc : c ≠ 0) :
    Measure.IsAddHaarMeasure
      (sourceHullHaar.map (fun x => c * x)) := by
  haveI : Measure.IsAddHaarMeasure sourceHullHaar := sourceHullHaar_isAddHaar
  have heq : (fun x : concreteLogShellField => c * x) = (mulAddEquiv c hc : _ → _) := rfl
  rw [heq]
  have hcont : Continuous (mulAddEquiv c hc : concreteLogShellField → concreteLogShellField) :=
    continuous_const.mul continuous_id
  have hinv : Continuous (mulAddEquiv c hc).symm :=
    continuous_const.mul continuous_id
  exact (mulAddEquiv c hc).isAddHaarMeasure_map sourceHullHaar hcont hinv

/-- **Exact missing (task-56 (1)): the Haar-uniqueness scalar step.**  For every nonzero
scaling, the pushforward measure is a scalar multiple of the actual Haar measure. -/
def S3135HaarUniquenessScalarStep : Prop :=
  ∀ (c : concreteLogShellField), c ≠ 0 →
    ∃ C : ENNReal, sourceHullHaar.map (fun x => c * x) = C • sourceHullHaar

/-- Status record for the F4 (b1) component chain. -/
def s3135HaarPushforwardReport : Audit.Obligation :=
  { id := "IUT-III.additive-haar-modulus-law-pushforward-half"
    source :=
      "IUT III Proposition 3.9(i) p.115; IUT III Remark 3.9.5(i) pp.158-159; " ++
        "IUT III Corollary 3.12 :10324-10353"
    status := Audit.VerificationStatus.interface
    note :=
      "LANDED: mulAddEquiv c hc (continuous additive automorphism of the actual " ++
        "concreteLogShellField for c != 0) and s3135_pushforward_isAddHaar " ++
        "((sourceHullHaar.map (fun x => c*x)).IsAddHaarMeasure, via Mathlib " ++
        "AddEquiv.isAddHaarMeasure_map).  EXACT MISSING: " ++
        "S3135HaarUniquenessScalarStep (mu' = C . mu for the pushforward).  Route: " ++
        "Mathlib integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport " ++
        "(Haar/Unique.lean:292) + Measure.ext on compactly-supported test functions.  " ++
        "CAUTION recorded: Measure.addHaarScalarFactor_smul (Haar/Unique.lean:323) is " ++
        "the scalar-factor-under-smul lemma, not the uniqueness equation (it caused " ++
        "the earlier quarantine).  Combined with S3135LogShellScalingIndex (index side, " ++
        "S3135HaarIndexActual) this yields S3135AdditiveHaarModulusLaw.  Owner: abc."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "S3135HaarUniquenessScalarStep",
        "S3135LogShellScalingIndex",
        "S3135AdditiveHaarModulusLaw" ] }

#check mulAddEquiv
#check s3135_pushforward_isAddHaar
#check S3135HaarUniquenessScalarStep

end LeanFormal.IUT.XiFPaper.S3135HaarPushforwardActual
end
