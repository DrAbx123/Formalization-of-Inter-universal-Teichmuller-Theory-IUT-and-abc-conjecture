import tmp.sheaf.xif.paper.S2055CompletionIntegralUnitsActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S2055CompletionIntegralUnitsActual
namespace LeanFormal.IUT.XiFPaper.S2056IsometricClosureActual
variable (place : NumberField.FinitePlace ℚ)
/-- The exact missing isometric algebraic-closure equivalence. -/
structure S2056ClosureIsometry where
  equiv : SourceAlgebraicClosure place ≃+* AlgebraicClosure ℚ_[completionRationalPrime place]
  norm_pres : ∀ x : SourceAlgebraicClosure place, ‖equiv x‖ = ‖x‖
noncomputable def S2056IntegersRingEquiv (I : S2056ClosureIsometry place) :
    Integers (SourceAlgebraicClosure place) ≃+*
      Integers (AlgebraicClosure ℚ_[completionRationalPrime place]) where
  toFun x := ⟨I.equiv (x : SourceAlgebraicClosure place), by
    rw [mem_integers_iff]
    rw [I.norm_pres]
    exact (mem_integers_iff _).mp x.property⟩
  invFun y := ⟨I.equiv.symm (y : AlgebraicClosure ℚ_[completionRationalPrime place]), by
    rw [mem_integers_iff]
    have h := I.norm_pres (I.equiv.symm (y : AlgebraicClosure ℚ_[completionRationalPrime place]))
    rw [I.equiv.apply_symm_apply] at h
    rw [← h]
    exact (mem_integers_iff _).mp y.property⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
noncomputable def S2056IntegralUnitsEquiv (I : S2056ClosureIsometry place) :
    S2055CompletionIntegralUnits place ≃* S2055QpIntegralUnits place :=
  Units.mapEquiv (S2056IntegersRingEquiv place I).toMulEquiv
theorem S2056IntegralUnitsIdentification_of_isometry
    (I : S2056ClosureIsometry place) :
    Nonempty (S2055IntegralUnitsIdentificationRequired place) :=
  ⟨S2056IntegralUnitsEquiv place I⟩
#check S2056ClosureIsometry
#check S2056IntegersRingEquiv
#check S2056IntegralUnitsEquiv
#check S2056IntegralUnitsIdentification_of_isometry
end LeanFormal.IUT.XiFPaper.S2056IsometricClosureActual
end
