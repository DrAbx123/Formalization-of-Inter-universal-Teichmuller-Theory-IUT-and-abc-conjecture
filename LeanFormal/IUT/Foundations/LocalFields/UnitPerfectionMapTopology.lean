import LeanFormal.IUT.Foundations.LocalFields.UnitPerfectionFunctoriality

/-!
# Continuous canonical maps of unit perfections

The map is continuous for the final topologies of original units and
integer denominators. Composition is checked on actual fractions.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {F G H : Type*} [NormedField F] [NormedField G] [NormedField H]
variable [IsUltrametricDist F] [IsUltrametricDist G] [IsUltrametricDist H]

theorem continuous_integralUnitMap (e : F →+* G) (he : Isometry e) :
    Continuous (integralUnitMap e he) := by
  have hring : Continuous (integralRingMap e he) :=
    (he.continuous.comp continuous_subtype_val).subtype_mk _
  apply Units.continuous_iff.mpr
  constructor
  · exact hring.comp Units.continuous_val
  · exact (hring.comp Units.continuous_val).comp continuous_inv

theorem unitPerfectionMap_comp (e : F →+* G) (he : Isometry e)
    (f : G →+* H) (hf : Isometry f) (x : UnitLogPerfection F) :
    unitPerfectionMap f hf (unitPerfectionMap e he x) =
      unitPerfectionMap (f.comp e) (hf.comp he) x := by
  induction x using LocalizedModule.induction_on with
  | _ u a =>
    change unitPerfectionMap f hf
      (unitPerfectionMap e he (LocalizedModule.mk (Additive.ofMul u.toMul) a)) =
      unitPerfectionMap (f.comp e) (hf.comp he)
        (LocalizedModule.mk (Additive.ofMul u.toMul) a)
    rw [unitPerfectionMap_mk, unitPerfectionMap_mk, unitPerfectionMap_mk]
    rfl

theorem continuous_unitPerfectionMap (e : F →+* G) (he : Isometry e) :
    letI := unitPerfectionTopology F
    letI := unitPerfectionTopology G
    Continuous (unitPerfectionMap e he) := by
  letI := unitPerfectionTopology F
  letI := unitPerfectionTopology G
  apply continuous_def.mpr
  intro s hs
  apply (isOpen_unitPerfectionTopology_iff _).mpr
  intro a
  have hs_a := (isOpen_unitPerfectionTopology_iff s).mp hs a
  have hp := hs_a.preimage (continuous_integralUnitMap e he)
  change IsOpen ((fun u : (Integers F)ˣ =>
    unitPerfectionMap e he (LocalizedModule.mk (Additive.ofMul u) a)) ⁻¹' s)
  simp_rw [unitPerfectionMap_mk]
  exact hp

end

end LeanFormal.IUT.LocalFieldLogarithm
