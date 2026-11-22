import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# Associativity of away localizations

Constructs the canonical R-algebra equivalence
`R[1/(f*(g*h))] ≃ₐ[R] R[1/((f*g)*h)]` from the equality of localizing elements.
This closes the associativity gap in the direct chart-to-triple map.
-/

noncomputable section

open scoped TensorProduct

namespace ABCBridge.TripleLocalizationAssociativity

universe u

variable {R : Type u} [CommRing R]

/-- The localizing elements are equal. -/
theorem mul_assoc_eq (f g h : R) : f * (g * h) = (f * g) * h :=
  mul_assoc f g h

/-- The canonical algebra equivalence between the two away localizations. -/
noncomputable def awayMulAssocAlgEquiv (f g h : R) :
    Localization.Away (f * (g * h)) ≃ₐ[R] Localization.Away ((f * g) * h) := by
  have hEq : f * (g * h) = (f * g) * h := mul_assoc f g h
  letI : IsLocalization (Submonoid.powers (f * (g * h)))
      (Localization.Away ((f * g) * h)) := by
    rw [hEq]
    infer_instance
  exact IsLocalization.algEquiv (Submonoid.powers (f * (g * h))) _ _

@[simp]
theorem awayMulAssocAlgEquiv_algebraMap (f g h : R) (r : R) :
    awayMulAssocAlgEquiv (R := R) f g h (algebraMap R (Localization.Away (f * (g * h))) r) =
      algebraMap R (Localization.Away ((f * g) * h)) r :=
  AlgEquiv.commutes _ r

@[simp]
theorem awayMulAssocAlgEquiv_symm_algebraMap (f g h : R) (r : R) :
    (awayMulAssocAlgEquiv (R := R) f g h).symm
        (algebraMap R (Localization.Away ((f * g) * h)) r) =
      algebraMap R (Localization.Away (f * (g * h))) r :=
  AlgEquiv.commutes _ r

/-- The corresponding scheme isomorphism of the two triple charts. -/
noncomputable def tripleChartAssocIso (f g h : R) :
    Spec (CommRingCat.of (Localization.Away (f * (g * h)))) ≅
      Spec (CommRingCat.of (Localization.Away ((f * g) * h))) :=
  Scheme.Spec.mapIso (awayMulAssocAlgEquiv (R := R) f g h).toRingEquiv.toCommRingCatIso

end ABCBridge.TripleLocalizationAssociativity