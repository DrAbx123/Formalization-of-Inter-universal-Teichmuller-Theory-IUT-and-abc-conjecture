import tmp.sheaf.n8.closure.C1InfiniteUnitQuotientAttempt
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# C1InfiniteDegreeSurjectiveAttempt

Tries to prove surjectivity of the infinite-place degree map
`(w.Completion)ˣ →* Multiplicative ℝ`, `u ↦ ofAdd (-log ‖u‖)`.

Real places: `v.Completion ≃+* ℝ` is an isometry; complex places:
`v.Completion ≃+* ℂ` is an isometry.  Use the real/complex scalar
`exp (-a)` as a unit and transport it back.  If the transport/norm lemmas are
not sufficient, leave the exact named obligation.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1InfiniteDegreeSurjectiveAttempt

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open LeanFormal.IUT.N8Closure.C1InfiniteUnitQuotientAttempt
open LeanFormal.IUT.N8Closure.C1UnitQuotientValueGroupAttempt
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F]

theorem infiniteUnitDegree_surjective_attempt
    (w : NumberField.InfinitePlace F) :
    Function.Surjective (infiniteUnitToValueGroup (F := F) w) := by
  intro r
  have hr : r = Multiplicative.ofAdd (Multiplicative.toAdd r) := by
    cases r; rfl
  rw [hr]
  rcases w.isReal_or_isComplex with hreal | hcomplex
  · let uR : ℝˣ :=
      Units.mk0 (Real.exp (-(Multiplicative.toAdd r))) (Real.exp_ne_zero _)
    let u : (w.Completion)ˣ :=
      Units.map ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm.toMonoidHom) uR
    refine ⟨u, ?_⟩
    change Multiplicative.ofAdd (-Real.log ‖(u : w.Completion)‖) =
      Multiplicative.ofAdd (Multiplicative.toAdd r)
    have huval : (u : w.Completion) =
        (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm (uR : ℝ) := rfl
    rw [huval]
    have hnorm2 :
        ‖(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm (uR : ℝ)‖ =
          ‖(uR : ℝ)‖ := by
      have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hreal).norm_map_of_map_zero
        (map_zero _) ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm (uR : ℝ))
      have hext :
          (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal)
              ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm (uR : ℝ)) =
            (uR : ℝ) := by
        rw [← NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
        exact (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).apply_symm_apply (uR : ℝ)
      rw [hext] at h
      exact h.symm
    rw [hnorm2]
    simp [uR, Real.log_exp]
  · let uC : ℂˣ :=
      Units.mk0 ((Real.exp (-(Multiplicative.toAdd r)) : ℝ) : ℂ)
        (by exact_mod_cast (Real.exp_ne_zero (-(Multiplicative.toAdd r))))
    let u : (w.Completion)ˣ :=
      Units.map ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex).symm.toMonoidHom) uC
    refine ⟨u, ?_⟩
    change Multiplicative.ofAdd (-Real.log ‖(u : w.Completion)‖) =
      Multiplicative.ofAdd (Multiplicative.toAdd r)
    have huval : (u : w.Completion) =
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex).symm (uC : ℂ) := rfl
    rw [huval]
    have hnorm2 :
        ‖(NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex).symm (uC : ℂ)‖ =
          ‖(uC : ℂ)‖ := by
      have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).norm_map_of_map_zero
        (map_zero _) ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex).symm (uC : ℂ))
      have hext :
          (NumberField.InfinitePlace.Completion.extensionEmbedding w)
              ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex).symm (uC : ℂ)) =
            (uC : ℂ) := by
        rw [← NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
        exact (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex).apply_symm_apply (uC : ℂ)
      rw [hext] at h
      exact h.symm
    rw [hnorm2]
    simp [uC, Complex.norm_exp, Real.log_exp]

/-- Since the degree map is actually surjective, the infinite unit quotient is
actually the archimedean value group. -/
theorem infiniteUnitQuotientEquiv_actual_closed
    (w : NumberField.InfinitePlace F) :
    InfiniteUnitQuotientEquivExists w :=
  ⟨infiniteUnitQuotientEquivOfSurjective (F := F) w
    (infiniteUnitDegree_surjective_attempt (F := F) w)⟩

end LeanFormal.IUT.N8Closure.C1InfiniteDegreeSurjectiveAttempt
