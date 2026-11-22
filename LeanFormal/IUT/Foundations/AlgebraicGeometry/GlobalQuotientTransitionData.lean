import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartCompat
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Localized affine quotient charts and overlap data

For a finite family `t : ι → R` and a finite etale `R`-algebra `A`, this file
records the actual localized quotient charts over `Away (t i)` and their
overlaps over `Away (t i * t j)`.  The transition comparison is the flat
base-change comparison proved in `GlobalQuotientChartCompat`.

Residual: the canonical tensor reassociation identifying
`Away(t_i t_j) ⊗_{Away(t_i)} (Away(t_i) ⊗_R A)` with `Away(t_i t_j) ⊗_R A`
is not constructed here; the chart/overlap covers and the base-change
comparison they induce are the gluing data consumed by the final consumer.
-/
namespace ABCBridge.GlobalQuotientTransitionData

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open ABCBridge.GlobalQuotientChartCompat

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The localized base at chart `i`. -/
abbrev baseLocal (t : ι → R) (i : ι) : Type u :=
  Localization.Away (t i)

/-- The localized base on the overlap of charts `i` and `j`. -/
abbrev baseOverlap (t : ι → R) (i j : ι) : Type u :=
  Localization.Away (t i * t j)

/-- The algebra `A` localized at chart `i`. -/
abbrev algLocal (t : ι → R) (i : ι) : Type u :=
  TensorProduct R (baseLocal t i) A

/-- The algebra `A` localized on the overlap of charts `i` and `j`. -/
abbrev algOverlap (t : ι → R) (i j : ι) : Type u :=
  TensorProduct R (baseOverlap t i j) A

/-- The actual affine quotient chart over `Away (t i)`. -/
noncomputable def chart (t : ι → R) (i : ι) :
    FiniteEtaleCover (baseSpec (R := baseLocal t i)) :=
  affineQuotientCoverGeneral (R := baseLocal t i) (A := algLocal t i) (G := G)

/-- The actual affine quotient overlap over `Away (t i * t j)`. -/
noncomputable def overlap (t : ι → R) (i j : ι) :
    FiniteEtaleCover (baseSpec (R := baseOverlap t i j)) :=
  affineQuotientCoverGeneral (R := baseOverlap t i j)
    (A := algOverlap t i j) (G := G)

/-- The flat base change of the `i`-chart to the overlap base. -/
noncomputable def chartRestricted (t : ι → R) (i j : ι) :
    FiniteEtaleCover (baseSpec (R := baseOverlap t i j)) :=
  affineQuotientBaseChangeActualCover
    (R := baseLocal t i) (A := algLocal t i) (G := G)
    (R' := baseOverlap t i j)

/-- The comparison of the restricted chart with the canonical overlap chart
after the flat base change.  This is the chart-level transition input. -/
noncomputable def chartRestrictedEquivOverlap (t : ι → R) (i j : ι) :
    chartRestricted (t := t) (i := i) (j := j) ≅ overlap t i j :=
  affineQuotientBaseChangeCoverEquiv
    (R := baseLocal t i) (A := algLocal t i) (G := G)
    (R' := baseOverlap t i j)

/-- Cocone compatibility data for the localized affine cover: the overlap
charts are canonically the restrictions of the chart covers.  This is stated
as a structure so that the global consumer can require exactly the still
missing tensor-reassociation field rather than a fake cover. -/
structure LocalizedAffineQuotientTransitionInput where
  reassocChart : ∀ i j,
    TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal t i) ≃ₐ[baseOverlap t i j]
      algOverlap t i j
  reassocOverlap : ∀ i j,
    TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal t j) ≃ₐ[baseOverlap t i j]
      algOverlap t i j


section TransitionProjections

/-- The restricted chart cover is finite etale over the overlap base. -/
theorem chartRestricted_finiteEtale (t : ι → R) (i j : ι) :
    Algebra.Etale (baseOverlap t i j)
      (fixedPointSubalgebra (baseOverlap t i j) (algOverlap t i j) G) ∧
      Module.Finite (baseOverlap t i j)
        (fixedPointSubalgebra (baseOverlap t i j) (algOverlap t i j) G) :=
  affineQuotientFixedPoint_finiteEtale
    (R := baseOverlap t i j) (A := algOverlap t i j) (G := G)

theorem chart_finiteEtale (t : ι → R) (i : ι) :
    Algebra.Etale (baseLocal t i)
      (fixedPointSubalgebra (baseLocal t i) (algLocal t i) G) ∧
      Module.Finite (baseLocal t i)
        (fixedPointSubalgebra (baseLocal t i) (algLocal t i) G) :=
  affineQuotientFixedPoint_finiteEtale
    (R := baseLocal t i) (A := algLocal t i) (G := G)

/-- The overlap comparison is an isomorphism of finite etale covers. -/
theorem chartRestrictedEquivOverlap_hom (t : ι → R) (i j : ι) :
    (chartRestrictedEquivOverlap (G := G) t i j).hom =
      (affineQuotientBaseChangeCoverEquiv (R := baseLocal t i)
        (A := algLocal t i) (G := G) (R' := baseOverlap t i j)).hom :=
  rfl

theorem chartRestrictedEquivOverlap_inv (t : ι → R) (i j : ι) :
    (chartRestrictedEquivOverlap (G := G) t i j).inv =
      (affineQuotientBaseChangeCoverEquiv (R := baseLocal t i)
        (A := algLocal t i) (G := G) (R' := baseOverlap t i j)).inv :=
  rfl

end TransitionProjections

end ABCBridge.GlobalQuotientTransitionData
