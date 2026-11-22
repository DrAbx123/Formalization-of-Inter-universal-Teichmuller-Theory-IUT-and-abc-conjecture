/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerInjection
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.RingTheory.Algebraic.Integral

/-!
  Continuity of the absolute Kummer class in the Galois variable.

  The absolute Galois group `Gal(K̄/K)` carries the Krull topology.  The
  coefficient group `μ_n(K̄)` is finite, hence is equipped with the discrete
  topology inside the discrete algebraic closure.  For each `a : Kˣ`, the
  Kummer class `σ ↦ σ α / α` is constant on the open stabilizer of the chosen
  root `α`, because the stabilizer of an algebraic element is open
  (`stabilizer_isOpen_of_isIntegral`).  Hence the class is locally constant,
  and therefore continuous for the discrete topology on `μ_n`.

  This is the "actual continuity" part of the Layer-2 Kummer realization: the
  coefficient module is discrete, so a crossed homomorphism with open
  stabilizers is a continuous cocycle.  No Frobenioid evaluation, Θ-link, or
  comparison with the group-theoretic Kummer isomorphism is asserted here.
-/

namespace LeanFormal.IUT

namespace AbsoluteKummerContinuity

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n]

/-- The absolute Kummer class is locally constant in the Galois variable. -/
theorem isLocallyConstant_absoluteKummerMap
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) (a : Kˣ) :
    IsLocallyConstant
      (fun σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K =>
        AbsoluteKummerInjection.absoluteKummerMap hμ a σ) := by
  letI : TopologicalSpace (AlgebraicClosure K) := ⊥
  haveI : DiscreteTopology (AlgebraicClosure K) := discreteTopology_bot _
  haveI : Algebra.IsIntegral K (AlgebraicClosure K) :=
    Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  haveI : ContinuousSMul (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (AlgebraicClosure K) :=
    continuousSMul_iff_stabilizer_isOpen.mpr
      (fun x => stabilizer_isOpen_of_isIntegral (K := K)
        (L := AlgebraicClosure K) x)
  rw [IsLocallyConstant.iff_exists_open]
  intro σ₀
  let α : (AlgebraicClosure K)ˣ :=
    AbsoluteKummerInjection.chosenRoot (K := K) (n := n) a
  let β : AlgebraicClosure K := (α : AlgebraicClosure K)
  let U : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
    {σ | σ • β = σ₀ • β}
  refine ⟨U, ?_, ?_, ?_⟩
  · have horbit : Continuous
        (fun σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K => σ • β) :=
      continuous_id.smul continuous_const
    have h := horbit.isOpen_preimage {σ₀ • β} (isOpen_discrete {σ₀ • β})
    convert h using 2
    ext σ
    rfl
  · rfl
  · intro σ hσ
    have hσ' : σ β = σ₀ β := by
      simpa [U, β, AlgEquiv.smul_def] using hσ
    simp only [AbsoluteKummerInjection.absoluteKummerMap_apply,
      KummerGaloisClass.kummerRatioHom_apply]
    apply Subtype.ext
    apply Units.ext
    simpa using hσ'

/-- With the discrete topology on the coefficient roots of unity, the absolute
Kummer class is a continuous function of the Galois automorphism. -/
theorem continuous_absoluteKummerMap
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) (a : Kˣ) :
    letI : TopologicalSpace (AlgebraicClosure K) := ⊥
    Continuous
      (fun σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K =>
        AbsoluteKummerInjection.absoluteKummerMap hμ a σ) := by
  letI : TopologicalSpace (AlgebraicClosure K) := ⊥
  exact (isLocallyConstant_absoluteKummerMap hμ a).continuous

end AbsoluteKummerContinuity

end LeanFormal.IUT
