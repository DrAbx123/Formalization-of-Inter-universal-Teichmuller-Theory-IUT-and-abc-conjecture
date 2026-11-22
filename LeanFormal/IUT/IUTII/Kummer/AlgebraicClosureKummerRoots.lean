/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Perfect

/-!
# Kummer roots and absolute-Galois fixed points in an algebraic closure

This file supplies the two absolute-level inputs used by the Kummer layer:

* `exists_root_algebraicClosure`: for a nonzero natural number `n`, every unit
  `a` of the base field has an `n`-th root among the units of an algebraic
  closure.  The root packages as a unit because its `n`-th power is the
  nonzero image of `a`.
* `fixed_by_absoluteGalois_mem_base`: over a field of characteristic zero,
  every element of an algebraic closure fixed by all `K`-automorphisms lies in
  the image of `K`.

The second statement uses that a field of characteristic zero is perfect, so
the algebraic closure is a separable closure, hence a Galois extension of `K`;
the fixed points of its full automorphism group are then computed by
`InfiniteGalois.mem_range_algebraMap_iff_fixed`.  No Galois action on the
chosen roots, irreducibility, or Kummer extension structure is asserted here.
-/

namespace LeanFormal.IUT

variable {K : Type*} [Field K]

/-- For `n ≠ 0`, every unit of `K` has an `n`-th root in the units of an
algebraic closure of `K`. -/
theorem exists_root_algebraicClosure (n : ℕ) [NeZero n] (a : Kˣ) :
    ∃ α : (AlgebraicClosure K)ˣ,
      α ^ n = Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (a : K)) hn
  have hz0 : z ≠ 0 := by
    intro hz_zero
    apply a.ne_zero
    apply FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)
    rw [map_zero, ← hz, hz_zero, zero_pow (NeZero.ne n)]
  refine ⟨Units.mk0 z hz0, ?_⟩
  ext
  simpa [Units.val_mk0] using hz

/-- Over a field of characteristic zero, an element of an algebraic closure
fixed by every `K`-automorphism lies in the image of `K`. -/
theorem fixed_by_absoluteGalois_mem_base [CharZero K] (x : AlgebraicClosure K)
    (hx : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ x = x) :
    x ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
  haveI : IsSepClosure K (AlgebraicClosure K) :=
    IsSepClosure.of_isAlgClosure_of_perfectField K (AlgebraicClosure K)
  haveI : IsGalois K (AlgebraicClosure K) := IsSepClosure.isGalois
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hx

end LeanFormal.IUT
