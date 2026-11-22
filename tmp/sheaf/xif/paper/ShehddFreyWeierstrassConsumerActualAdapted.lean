import LeanFormal.IUT.ABCBridge.Geometry.FreyWeierstrassCurve

/-!
# ShehddFreyWeierstrassConsumerActualAdapted — Frey Weierstrass model consumer

STEP 0 prior-art (reuse only; A475 search: Frey Weierstrass model found):
* ABCBridge/Geometry/FreyWeierstrassCurve.lean: freyWeierstrassCurve,
  freyWeierstrassCurve_equation, _b₂/b₄/b₆/b₈, _c₄/c₆, _discriminant(+_square),
  _discriminant_of_add_eq, _c₄_swap/_c₆_swap/_discriminant_swap,
  _c₄_scale/_c₆_scale/_discriminant_scale, _isElliptic_of_isUnit, _map_comp/_map_discriminant.

This file packages the Frey model invariants, scaling behavior and ellipticity criterion as
one consumer for the ABC Frey specialization.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddFreyWeierstrassConsumerActualAdapted

open LeanFormal.IUT

universe u

variable {R : Type u} [CommRing R]

/-- **PROVED consumer:** the Frey model discriminant, square form, c₄ and c₆. -/
theorem freyWeierstrass_invariants_consumer (a b : R) :
    (freyWeierstrassCurve a b).Δ = 16 * a ^ 2 * b ^ 2 * (a + b) ^ 2 ∧
      (freyWeierstrassCurve a b).Δ = (4 * a * b * (a + b)) ^ 2 ∧
        (freyWeierstrassCurve a b).c₄ = 16 * (a ^ 2 + a * b + b ^ 2) :=
  ⟨freyWeierstrassCurve_discriminant a b,
    freyWeierstrassCurve_discriminant_square a b,
    freyWeierstrassCurve_c₄ a b⟩

/-- **PROVED consumer:** the abc-additive substitution and the weight-2/3/6 scaling laws. -/
theorem freyWeierstrass_scaling_consumer (a b c scale : R) (hadd : a + b = c) :
    (freyWeierstrassCurve a b).Δ = 16 * a ^ 2 * b ^ 2 * c ^ 2 ∧
      (freyWeierstrassCurve (scale * a) (scale * b)).c₄ =
        scale ^ 2 * (freyWeierstrassCurve a b).c₄ ∧
        (freyWeierstrassCurve (scale * a) (scale * b)).c₆ =
          scale ^ 3 * (freyWeierstrassCurve a b).c₆ ∧
          (freyWeierstrassCurve (scale * a) (scale * b)).Δ =
            scale ^ 6 * (freyWeierstrassCurve a b).Δ :=
  ⟨freyWeierstrassCurve_discriminant_of_add_eq a b c hadd,
    freyWeierstrassCurve_c₄_scale a b scale,
    freyWeierstrassCurve_c₆_scale a b scale,
    freyWeierstrassCurve_discriminant_scale a b scale⟩

/-- **PROVED consumer:** the unit-based ellipticity criterion for the Frey model. -/
theorem freyWeierstrass_isElliptic_consumer (a b : R) (htwo : IsUnit (2 : R))
    (ha : IsUnit a) (hb : IsUnit b) (hab : IsUnit (a + b)) :
    (freyWeierstrassCurve a b).IsElliptic :=
  freyWeierstrassCurve_isElliptic_of_isUnit a b htwo ha hb hab

/-- Row record: reused Frey-model assets vs the consumer bundles. -/
def freyWeierstrassRows : List (String × String × String) :=
  [ ("equation equivalence y² = x(x-a)(x+b)", "REUSED PROVED", "freyWeierstrassCurve_equation")
  , ("invariants b/c/discriminant (+square form)", "REUSED PROVED", "freyWeierstrassCurve_b*/c*/discriminant*")
  , ("additive substitution and scaling weights 2/3/6", "REUSED PROVED", "_discriminant_of_add_eq / _c₄_scale / _c₆_scale / _discriminant_scale")
  , ("swap and zero-parameter specializations", "REUSED PROVED", "_c₄_swap / _c₆_swap / _discriminant_swap / _discriminant_of_(left|right|add)_eq_zero")
  , ("unit ellipticity criterion + map compatibility", "REUSED PROVED", "freyWeierstrassCurve_isElliptic_of_isUnit / _map_comp / _map_discriminant")
  , ("consumer bundles", "COMPOSED PROVED", "freyWeierstrass_invariants_consumer, freyWeierstrass_scaling_consumer, freyWeierstrass_isElliptic_consumer") ]

theorem freyWeierstrassRows_length : freyWeierstrassRows.length = 6 := rfl

#check freyWeierstrass_invariants_consumer
#check freyWeierstrass_scaling_consumer
#check freyWeierstrass_isElliptic_consumer
#check freyWeierstrassRows_length

end LeanFormal.IUT.XiFPaper.ShehddFreyWeierstrassConsumerActualAdapted
end
