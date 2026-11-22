/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerInjection
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
  The Kummer injection on the quotient `Kˣ / (Kˣ)^n`.

  `AbsoluteKummerInjection` proves that the absolute Kummer class
  `a ↦ (σ ↦ σ α / α)` has kernel exactly the subgroup of `n`-th powers in
  `Kˣ`.  This file packages that statement on the quotient group: the class
  descends to `Kˣ ⧸ (Kˣ)^n` and the induced homomorphism is injective.

  The codomain is `Hom(Gal(K̄/K), μ_n(K̄))`, which is the continuous first
  cohomology `H¹(G_K, μ_n)` for the trivial action on the discrete coefficient
  group `μ_n`.  No surjectivity or identification of the image is asserted.
-/

namespace LeanFormal.IUT

namespace AbsoluteKummerQuotient

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n]

/-- The subgroup of `n`-th powers in `Kˣ`. -/
def nthPowerSubgroup : Subgroup Kˣ :=
  (powMonoidHom n).range

/-- Membership in `nthPowerSubgroup` is existence of an `n`-th root in `Kˣ`. -/
@[simp] theorem mem_nthPowerSubgroup (a : Kˣ) :
    a ∈ nthPowerSubgroup (K := K) (n := n) ↔ ∃ b : Kˣ, b ^ n = a := by
  simp [nthPowerSubgroup, powMonoidHom]

/-- The absolute Kummer class descended to `Kˣ ⧸ (Kˣ)^n`. -/
noncomputable def absoluteKummerMapQuotient
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    (Kˣ ⧸ nthPowerSubgroup (K := K) (n := n)) →*
      ((AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
        rootsOfUnity n (AlgebraicClosure K)) :=
  QuotientGroup.lift (nthPowerSubgroup (K := K) (n := n))
    (AbsoluteKummerInjection.absoluteKummerMap hμ) (by
      intro a ha
      exact (AbsoluteKummerInjection.absoluteKummerMap_eq_one_iff hμ a).mpr
        ((mem_nthPowerSubgroup a).mp ha))

/-- The descended map is computed by the absolute Kummer map on a
representative. -/
@[simp] theorem absoluteKummerMapQuotient_mk
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n))
    (a : Kˣ) :
    absoluteKummerMapQuotient (K := K) (n := n) hμ
        (QuotientGroup.mk a) =
      AbsoluteKummerInjection.absoluteKummerMap hμ a :=
  by rw [absoluteKummerMapQuotient, QuotientGroup.lift_mk]

/-- The Kummer map on `Kˣ ⧸ (Kˣ)^n` is injective: two units have the same
Kummer class exactly when their quotient is an `n`-th power. -/
theorem absoluteKummerMapQuotient_injective
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    Function.Injective
      (absoluteKummerMapQuotient (K := K) (n := n) hμ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | _ a =>
      rw [MonoidHom.mem_ker, absoluteKummerMapQuotient, QuotientGroup.lift_mk] at hx
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
      exact (mem_nthPowerSubgroup a).mpr
        ((AbsoluteKummerInjection.absoluteKummerMap_eq_one_iff hμ a).mp hx)

end AbsoluteKummerQuotient

end LeanFormal.IUT
