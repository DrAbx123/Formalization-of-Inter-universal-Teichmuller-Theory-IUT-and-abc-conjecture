import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.PermutationTorsorQuotient
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import Mathlib.Tactic

/-!
# Finite etale quotient in the free regular action case

For the regular permutation cover Spec (G -> R) over Spec R, the fixed-point
algebra is R itself: sections invariant under the regular G-action are constant.
Consequently the fixed-point subalgebra is finite etale over R.  This module
packages the actual finite etale quotient cover for the transport consumer and
does not use the legacy coverAction triviality chain.
-/

noncomputable section

namespace ABCBridge.FiniteEtaleQuotientFreeAction

open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [Fintype G]

/-- The invariant sections of the regular permutation cover are the constants,
hence equivalent to R. -/
noncomputable def regularPermutationSectionsEquiv :
    FixedPoints.subalgebra R (G → R) G ≃ₐ[R] R :=
  PermutationTorsorQuotient.regular_fixedPoints_equiv (R := R) (G := G)

/-- The fixed-point subalgebra of the regular permutation cover is etale over R. -/
theorem regularPermutationFixedPoints_etale :
    Algebra.Etale R (FixedPoints.subalgebra R (G → R) G) :=
  PermutationTorsorQuotient.regular_fixedPoints_etale (R := R) (G := G)

/-- The fixed-point subalgebra of the regular permutation cover is finite over R. -/
theorem regularPermutationFixedPoints_moduleFinite :
    Module.Finite R (FixedPoints.subalgebra R (G → R) G) :=
  PermutationTorsorQuotient.regular_fixedPoints_moduleFinite (R := R) (G := G)

/-- The regular fixed-point quotient is finite etale over R. -/
theorem regularPermutationFixedPoints_finiteEtale :
    Algebra.Etale R (FixedPoints.subalgebra R (G → R) G) ∧
      Module.Finite R (FixedPoints.subalgebra R (G → R) G) :=
  ⟨regularPermutationFixedPoints_etale (R := R) (G := G),
    regularPermutationFixedPoints_moduleFinite (R := R) (G := G)⟩

/-- The actual regular permutation cover Spec (G -> R) over Spec R. -/
noncomputable def regularPermutationCover :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  AffineLocalQuotientGluingConstruct.regularPermutationCover R G

/-- The actual fixed-point quotient cover Spec ((G -> R)^G) over Spec R. -/
noncomputable def regularQuotientCover :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  AffineLocalQuotientGluingConstruct.regularPermutationQuotientCover R G

/-- The chart map from the regular permutation cover to its fixed-point quotient. -/
noncomputable def regularQuotientChartMap :
    regularPermutationCover (R := R) (G := G) ⟶
      regularQuotientCover (R := R) (G := G) :=
  AffineLocalQuotientGluingConstruct.regularPermutationChartMap R G

/-- Transport-facing finite etale quotient cover in the free regular action case.
All fields are actual: no residual and no triviality hypothesis. -/
structure AffineFiniteEtaleQuotientCover
    (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] where
  cover : FiniteEtaleCover (Spec (CommRingCat.of R))
  quotientCover : FiniteEtaleCover (Spec (CommRingCat.of R))
  chartMap : cover ⟶ quotientCover
  sectionsEquiv : FixedPoints.subalgebra R (G → R) G ≃ₐ[R] R
  quotient_etale : Algebra.Etale R (FixedPoints.subalgebra R (G → R) G)
  quotient_finite : Module.Finite R (FixedPoints.subalgebra R (G → R) G)

/-- The actual transport-facing quotient cover for the regular permutation cover. -/
noncomputable def regularAffineFiniteEtaleQuotientCover :
    AffineFiniteEtaleQuotientCover R G where
  cover := regularPermutationCover (R := R) (G := G)
  quotientCover := regularQuotientCover (R := R) (G := G)
  chartMap := regularQuotientChartMap (R := R) (G := G)
  sectionsEquiv := regularPermutationSectionsEquiv (R := R) (G := G)
  quotient_etale := regularPermutationFixedPoints_etale (R := R) (G := G)
  quotient_finite := regularPermutationFixedPoints_moduleFinite (R := R) (G := G)

/-- The regular quotient cover is the actual fixed-point quotient cover. -/
theorem regularAffineFiniteEtaleQuotientCover_quotientCover :
    (regularAffineFiniteEtaleQuotientCover (R := R) (G := G)).quotientCover =
      regularQuotientCover (R := R) (G := G) :=
  rfl

/-- The regular quotient cover is etale over R. -/
theorem regularAffineFiniteEtaleQuotientCover_etale :
    Algebra.Etale R (FixedPoints.subalgebra R (G → R) G) :=
  (regularAffineFiniteEtaleQuotientCover (R := R) (G := G)).quotient_etale

/-- The regular quotient cover is finite over R. -/
theorem regularAffineFiniteEtaleQuotientCover_finite :
    Module.Finite R (FixedPoints.subalgebra R (G → R) G) :=
  (regularAffineFiniteEtaleQuotientCover (R := R) (G := G)).quotient_finite

/-- Complete regular free-action package: invariant sections, etaleness and
finiteness, and the transport-facing quotient cover. -/
theorem regularAffineFiniteEtaleQuotientCover_complete :
    Nonempty (FixedPoints.subalgebra R (G → R) G ≃ₐ[R] R) ∧
      Algebra.Etale R (FixedPoints.subalgebra R (G → R) G) ∧
      Module.Finite R (FixedPoints.subalgebra R (G → R) G) :=
  ⟨⟨regularPermutationSectionsEquiv (R := R) (G := G)⟩,
    regularPermutationFixedPoints_etale (R := R) (G := G),
    regularPermutationFixedPoints_moduleFinite (R := R) (G := G)⟩

end ABCBridge.FiniteEtaleQuotientFreeAction