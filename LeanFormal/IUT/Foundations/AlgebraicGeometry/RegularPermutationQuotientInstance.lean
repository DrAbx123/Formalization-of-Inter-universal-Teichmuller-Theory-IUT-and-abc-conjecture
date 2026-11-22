import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientFreeAction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration

/-!
# Regular permutation quotient instance

For the regular permutation cover Spec(G -> R), the affine finite-etale
quotient construction of AffineQuotientIntegration applies to the coordinate
algebra G -> R.  Its quotient Spec((G -> R)^G) is exactly the existing regular
quotient cover, and its projection is the regular quotient chart map.  The
sections of the cover are identified with G -> R by the green frontend
regularPermutationSectionsEquiv and Scheme.GammaSpecIso.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientInstance

universe u

open ABCBridge.FiniteEtaleQuotientFreeAction
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [Fintype G]

/-- The regular permutation sections algebra is G -> R. -/
noncomputable def regularSectionsAlgebraEquiv :
    Γ((regularPermutationCover (R := R) (G := G)).carrier, ⊤) ≃+* (G → R) :=
  (Scheme.ΓSpecIso (CommRingCat.of (G → R))).commRingCatIsoToRingEquiv

/-- The fixed-point algebra used by the regular quotient instance. -/
abbrev regularFixedAlgebra : Type u :=
  FixedPoints.subalgebra R (G → R) G

/-- The affine quotient construction specialized to the regular sections
algebra. -/
noncomputable def regularAffineQuotient :
    AffineFiniteEtaleQuotient (R := R) (G := G) (A := (G → R)) :=
  affineFiniteEtaleQuotient (R := R) (G := G) (A := (G → R))

/-- The affine quotient scheme Spec((G -> R)^G) is the carrier of the existing
regular quotient cover. -/
noncomputable def specFixedPointsIsoRegularQuotient :
    Spec (CommRingCat.of (regularFixedAlgebra (R := R) (G := G))) ≅
      (regularQuotientCover (R := R) (G := G)).carrier :=
  Iso.refl _

/-- The projection of the affine quotient is the fixed-point inclusion. -/
theorem affineProjection_eq_fixedInclusion :
    (regularAffineQuotient (R := R) (G := G)).projection =
      Spec.map (CommRingCat.ofHom
        (Subalgebra.val (FixedPoints.subalgebra R (G → R) G))) :=
  rfl

/-- The existing regular quotient chart map has the same underlying projection. -/
theorem regularQuotientChartMap_eq_fixedInclusion :
    (regularQuotientChartMap (R := R) (G := G)).hom.left =
      Spec.map (CommRingCat.ofHom
        (Subalgebra.val (FixedPoints.subalgebra R (G → R) G))) :=
  rfl

/-- The regular quotient chart map is the affine quotient projection. -/
theorem regularQuotientChartMap_eq_affineProjection :
    (regularQuotientChartMap (R := R) (G := G)).hom.left =
      (regularAffineQuotient (R := R) (G := G)).projection := by
  rfl

/-- The regular fixed-point quotient is the affine quotient scheme. -/
theorem regularQuotientCover_eq_affineQuotientScheme :
    (regularQuotientCover (R := R) (G := G)).carrier =
      affineQuotientScheme (R := R) (G := G) (G → R) :=
  rfl

/-- The affine finite-etale quotient has the expected cover projection and
quotient scheme. -/
theorem regularPermutationQuotientInstance_spec :
    (regularQuotientCover (R := R) (G := G)).carrier =
        affineQuotientScheme (R := R) (G := G) (G → R) ∧
      (regularQuotientChartMap (R := R) (G := G)).hom.left =
        (regularAffineQuotient (R := R) (G := G)).projection ∧
      Nonempty (Γ((regularPermutationCover (R := R) (G := G)).carrier, ⊤) ≃+*
        (G → R)) :=
  ⟨regularQuotientCover_eq_affineQuotientScheme R G,
    regularQuotientChartMap_eq_affineProjection R G,
    ⟨regularSectionsAlgebraEquiv R G⟩⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientInstance
