import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Tactic

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace LeanFormal.IUT.XiFPaper.Mzk1SchemePreimagePullbackIsoActual

/-!
# Preimage of an open subscheme under a pullback projection

For `f : X ⟶ Y`, `g : Z ⟶ Y` and an open subscheme `U : X.Opens`, the preimage
`pullback.fst f g ⁻¹ᵁ U` in `pullback f g` is isomorphic to the pullback
`U ×_Y Z = pullback (U.ι ≫ f) g`: fiber products commute with restriction to
an open subscheme.
-/

/-- The square over `U`: restricting the first projection of `pullback f g` to the open
subscheme `pullback.fst f g ⁻¹ᵁ U`, together with the second projection, is cartesian,
exhibiting `pullback.fst f g ⁻¹ᵁ U` as `U ×_Y Z`. -/
theorem isPullback_preimage {X Y Z : Scheme} (f : X ⟶ Y) (g : Z ⟶ Y) (U : X.Opens) :
    IsPullback (pullback.fst f g ∣_ U) ((pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.snd f g)
      (U.ι ≫ f) g :=
  (isPullback_morphismRestrict (pullback.fst f g) U).paste_vert
    (IsPullback.of_hasPullback f g)

/-- Preimage of an open subscheme is the pullback of the restricted map. -/
noncomputable def preimagePullbackIso {X Y Z : Scheme} (f : X ⟶ Y) (g : Z ⟶ Y) (U : X.Opens) :
    (pullback.fst f g ⁻¹ᵁ U).toScheme ≅ pullback (U.ι ≫ f) g :=
  (isPullback_preimage f g U).isoPullback

/-- Compatibility of the isomorphism with the first projection. -/
theorem preimagePullbackIso_hom_fst {X Y Z : Scheme} (f : X ⟶ Y) (g : Z ⟶ Y)
    (U : X.Opens) :
    (preimagePullbackIso f g U).hom ≫ pullback.fst (U.ι ≫ f) g
      = pullback.fst f g ∣_ U :=
  IsPullback.isoPullback_hom_fst (isPullback_preimage f g U)

#print axioms isPullback_preimage
#print axioms preimagePullbackIso
#print axioms preimagePullbackIso_hom_fst

end LeanFormal.IUT.XiFPaper.Mzk1SchemePreimagePullbackIsoActual
