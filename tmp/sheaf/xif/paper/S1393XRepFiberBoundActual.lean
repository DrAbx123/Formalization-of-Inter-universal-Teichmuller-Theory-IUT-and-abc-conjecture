/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Fibres of the `x`-coordinate map on an affine Weierstrass curve

This file ports, essentially verbatim, the two combinatorial lemmas from Tau Ceti's
`TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/DivisionPolynomialSeparable.lean`
(commit `df319cee080d8cab30699ff8ab3ed8d9347768aa`, Lean v4.36.0-rc1) that bound the fibres of
the `x`-coordinate map `P ↦ P.xRep` on the nonsingular points of an affine Weierstrass curve,
and that place the abscissae of a finite set of such points among the roots of a nonzero
polynomial.

Only these two lemmas are ported; no other part of Tau Ceti is imported or vendored.  The
statements are specialised to the current Mathlib API, where `WeierstrassCurve.Affine.Point`
is available directly for an affine curve over a field, rather than through the
`(W ⁄ F).toAffine` base-change wrapper used in Tau Ceti.

## Main results

* `WeierstrassCurve.card_filter_xRep_le_two`: at most two points of a finite set have a
  prescribed `xRep`.
* `WeierstrassCurve.mem_image_xRep`: the `xRep` of a point whose coordinates are roots of a
  nonzero polynomial `p` lies in the image of the roots of `p` under `x ↦ ![x, 1]`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

open Finset Polynomial WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-- **At most two points share an abscissa**: a point is determined by its abscissa up to sign. -/
theorem card_filter_xRep_le_two [DecidableEq F] {V : WeierstrassCurve.Affine F}
    (s : Finset V.Point) (b : Fin 2 → F) : #{P ∈ s | P.xRep = b} ≤ 2 := by
  rcases Finset.eq_empty_or_nonempty {P ∈ s | P.xRep = b} with h | ⟨Q, hQ⟩
  · simp [h]
  · have hsub : {P ∈ s | P.xRep = b} ⊆ {Q, -Q} := by
      intro P hP
      have hb : P.xRep = Q.xRep := by
        rw [(Finset.mem_filter.mp hP).2, (Finset.mem_filter.mp hQ).2]
      rcases Point.eq_or_eq_neg_of_xRep_eq_xRep hb with h | h <;> simp [h]
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))

/-- The abscissae of a set of points, as a `Finset` of the roots of `p`. -/
theorem mem_image_xRep [DecidableEq F] {V : WeierstrassCurve.Affine F} {p : F[X]}
    {T : Finset V.Point}
    (h : ∀ P ∈ T, ∃ x y, ∃ hns : V.Nonsingular x y,
      P = Affine.Point.some x y hns ∧ p.eval x = 0) (hp : p ≠ 0) :
    ∀ P ∈ T, P.xRep ∈ p.roots.toFinset.image (fun x : F ↦ ![x, 1]) := by
  intro P hP
  obtain ⟨x, y, hns, rfl, hx⟩ := h P hP
  exact Finset.mem_image.mpr
    ⟨x, Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hp, hx⟩), (Point.xRep_some hns).symm⟩

end WeierstrassCurve

end
