/-
S2858: the global chart-alpha self-map of the fixed E37 projective scheme squares
to the identity.

The global self-map `globalAlphaScheme K` of `S2820E37ProjectiveScheme K` is the
gluing of

* chart Z: `S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K`,
* chart Y: `chartYNegGlued K`.

Its square is checked on the two charts of the glue data
`D K = E37ProjGlueData K (S2820E37TransitionIso K)`:

* chart Z: the chart-Z substitution `(x, y) ↦ (x, -y - 1)` is an involution,
  hence `S2853ChartZSchemeEndo K ≫ S2853ChartZSchemeEndo K = 𝟙 _`;
* chart Y: after restricting to the chart-Y cover `chartYCover K`,
  - on `D(t)` (the `g1Ring` piece) the square follows from
    `g1Ring K = alpha K ∘ S2853RingHom K` plus the chart-Z involution and the
    projective glue condition `glue_condition_formula`;
  - on `D(1 + t)` (the `g0Ring` piece) the chart-Y negation
    `s ↦ -s/(1+t), t ↦ -t/(1+t)` is an involution on the localization
    `Away (1 + t)`, which yields `sigma ∘ g0Ring = algebraMap` and hence
    the second iteration of `g0Scheme` is the inclusion `f0`.
-/

import tmp.sheaf.xif.paper.S2857GlobalAlphaCompatActual
import tmp.sheaf.xif.paper.S2856HfYZRingActual
import tmp.sheaf.xif.paper.S2856HfOverlapActual
import tmp.sheaf.xif.paper.S2853E37NegationAutomorphismActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
open LeanFormal.IUT.XiFPaper.S2856HfOverlapActual
open LeanFormal.IUT.XiFPaper.S2856HfYZRingActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaCompatActual
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace LeanFormal.IUT.XiFPaper.S2858AlphaSquareActual

variable (K : Type) [Field K] [DecidableEq K]

/-! ## 1. The chart-Z substitution is an involution -/

theorem S2853RingHom_comp_self :
    (S2853RingHom K).comp (S2853RingHom K) =
      RingHom.id (S2801E37CoordinateRing K) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [S2853RingHom, S2853PolyHom, S2853Subst]
  · intro i
    fin_cases i <;> simp [S2853RingHom, S2853PolyHom, S2853Subst]

/-- The chart-Z negation endomorphism of the affine chart is an involution. -/
theorem chartZSchemeEndo_sq :
    S2853ChartZSchemeEndo K ≫ S2853ChartZSchemeEndo K =
      𝟙 (S2801E37AffineScheme K) := by
  unfold S2853ChartZSchemeEndo
  rw [← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp]
  rw [S2853RingHom_comp_self]
  simp

/-! ## 2. The chart-Y negation is an involution on the chart-Y piece -/

/-- `1 + t'` for the chart-Y negation is the inverse of `1 + t`:
the chart-Y negation `(s, t) ↦ (-s/(1+t), -t/(1+t))` sends `1 + t` to
`1/(1+t)`. -/
theorem one_add_chartYNegT :
    1 + S2853ChartYNegT K = ↑((S2853ChartYNegUnit K)⁻¹) := by
  have hu : (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) =
      1 + algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K) := by
    rw [show (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) =
      algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (1 + S2853ChartYT K) from
      IsUnit.unit_spec _]
    rw [map_add, map_one]
  have hAv : algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K) *
      ↑((S2853ChartYNegUnit K)⁻¹) = 1 - ↑((S2853ChartYNegUnit K)⁻¹) := by
    have hA : algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K) =
        (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) - 1 := by
      rw [hu]; ring
    rw [hA, sub_mul, Units.mul_inv, one_mul]
  have hT : S2853ChartYNegT K =
      -(algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K)) *
        ↑((S2853ChartYNegUnit K)⁻¹) := by
    rw [show S2853ChartYNegT K = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
      (-(S2853ChartYT K)) * ↑((S2853ChartYNegUnit K)⁻¹) from rfl]
    rw [map_neg]
  rw [hT]
  calc 1 + -(algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K)) *
        ↑((S2853ChartYNegUnit K)⁻¹)
      = 1 - algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K) *
          ↑((S2853ChartYNegUnit K)⁻¹) := by ring
    _ = 1 - (1 - ↑((S2853ChartYNegUnit K)⁻¹)) := by rw [hAv]
    _ = ↑((S2853ChartYNegUnit K)⁻¹) := by ring

/-- `1 + t'` is a unit, read through `g0Ring`. -/
theorem g0Ring_one_add_tY_isUnit : IsUnit (g0Ring K (1 + tY K)) := hU K

/-- The second iteration of the chart-Y negation, as an endomorphism of the
localization `Away (1 + t)`. -/
noncomputable def sigmaRing (K : Type) [Field K] [DecidableEq K] :
    S2853ChartYNegRing K →+* S2853ChartYNegRing K :=
  IsLocalization.Away.lift (S := S2853ChartYNegRing K) (x := 1 + tY K)
    (g := g0Ring K) (g0Ring_one_add_tY_isUnit K)

theorem sigmaRing_algebraMap (a : E37ChartYRing K) :
    sigmaRing K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) a) = g0Ring K a :=
  IsLocalization.Away.lift_eq (x := 1 + tY K) (g := g0Ring K) (g0Ring_one_add_tY_isUnit K) a

theorem sigmaRing_comp_algebraMap :
    (sigmaRing K).comp (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)) = g0Ring K :=
  IsLocalization.Away.lift_comp (x := 1 + tY K) (g := g0Ring K) (g0Ring_one_add_tY_isUnit K)

/-- The chart-Y negation sends `1 + t` to its inverse. -/
theorem sigmaRing_unit :
    sigmaRing K (↑(S2853ChartYNegUnit K)) = ↑((S2853ChartYNegUnit K)⁻¹) := by
  have hu : (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) =
      algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (1 + S2853ChartYT K) :=
    IsUnit.unit_spec _
  rw [hu, sigmaRing_algebraMap, map_add, map_one, g0Ring_apply_t, one_add_chartYNegT]

/-- The chart-Y negation sends the inverse of `1 + t` back to `1 + t`. -/
theorem sigmaRing_unit_inv :
    sigmaRing K (↑((S2853ChartYNegUnit K)⁻¹)) = ↑(S2853ChartYNegUnit K) := by
  have h1 : sigmaRing K (↑((S2853ChartYNegUnit K)⁻¹)) *
      sigmaRing K (↑(S2853ChartYNegUnit K)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [sigmaRing_unit] at h1
  have h2 : (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) *
      ↑((S2853ChartYNegUnit K)⁻¹) = 1 := Units.mul_inv _
  have h3 : sigmaRing K (↑((S2853ChartYNegUnit K)⁻¹)) *
        ↑((S2853ChartYNegUnit K)⁻¹) =
      (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) *
        ↑((S2853ChartYNegUnit K)⁻¹) := by
    rw [h1, h2]
  exact (IsUnit.mul_left_inj (show IsUnit (↑((S2853ChartYNegUnit K)⁻¹) :
    S2853ChartYNegRing K) from ⟨(S2853ChartYNegUnit K)⁻¹, rfl⟩)).mp h3

/-- The chart-Y negation, applied to the `s`-coordinate image, returns `s`. -/
theorem sigmaRing_negS :
    sigmaRing K (S2853ChartYNegS K) =
      algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K) := by
  have hS : S2853ChartYNegS K =
      algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (-(S2853ChartYS K)) *
        ↑((S2853ChartYNegUnit K)⁻¹) := rfl
  calc sigmaRing K (S2853ChartYNegS K)
      = sigmaRing K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (-(S2853ChartYS K)) * ↑((S2853ChartYNegUnit K)⁻¹)) := by rw [hS]
    _ = sigmaRing K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (-(S2853ChartYS K))) * sigmaRing K (↑((S2853ChartYNegUnit K)⁻¹)) := by
        rw [map_mul]
    _ = sigmaRing K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (-(S2853ChartYS K))) * ↑(S2853ChartYNegUnit K) := by rw [sigmaRing_unit_inv]
    _ = sigmaRing K (-(algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (S2853ChartYS K))) * ↑(S2853ChartYNegUnit K) := by
        rw [RingHom.map_neg (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)) (S2853ChartYS K)]
    _ = (-sigmaRing K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (S2853ChartYS K))) * ↑(S2853ChartYNegUnit K) := by
        rw [RingHom.map_neg (sigmaRing K) (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (S2853ChartYS K))]
    _ = (-g0Ring K (S2853ChartYS K)) * ↑(S2853ChartYNegUnit K) := by rw [sigmaRing_algebraMap]
    _ = (-S2853ChartYNegS K) * ↑(S2853ChartYNegUnit K) := by rw [g0Ring_apply_s]
    _ = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K) := by
        rw [show S2853ChartYNegS K = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (-(S2853ChartYS K)) * ↑((S2853ChartYNegUnit K)⁻¹) from rfl]
        rw [RingHom.map_neg (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)) (S2853ChartYS K)]
        calc (-(-algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K) *
              ↑((S2853ChartYNegUnit K)⁻¹))) * ↑(S2853ChartYNegUnit K)
            = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K) *
                (↑((S2853ChartYNegUnit K)⁻¹) * ↑(S2853ChartYNegUnit K)) := by ring
          _ = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K) * 1 := by
              rw [Units.inv_mul]
          _ = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K) := by
              rw [mul_one]

/-- The chart-Y negation, applied to the `t`-coordinate image, returns `t`. -/
theorem sigmaRing_negT :
    sigmaRing K (S2853ChartYNegT K) =
      algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K) := by
  have hT : S2853ChartYNegT K =
      algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (-(S2853ChartYT K)) *
        ↑((S2853ChartYNegUnit K)⁻¹) := rfl
  calc sigmaRing K (S2853ChartYNegT K)
      = sigmaRing K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (-(S2853ChartYT K)) * ↑((S2853ChartYNegUnit K)⁻¹)) := by rw [hT]
    _ = sigmaRing K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (-(S2853ChartYT K))) * sigmaRing K (↑((S2853ChartYNegUnit K)⁻¹)) := by
        rw [map_mul]
    _ = sigmaRing K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (-(S2853ChartYT K))) * ↑(S2853ChartYNegUnit K) := by rw [sigmaRing_unit_inv]
    _ = sigmaRing K (-(algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (S2853ChartYT K))) * ↑(S2853ChartYNegUnit K) := by
        rw [RingHom.map_neg (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)) (S2853ChartYT K)]
    _ = (-sigmaRing K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (S2853ChartYT K))) * ↑(S2853ChartYNegUnit K) := by
        rw [RingHom.map_neg (sigmaRing K) (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (S2853ChartYT K))]
    _ = (-g0Ring K (S2853ChartYT K)) * ↑(S2853ChartYNegUnit K) := by rw [sigmaRing_algebraMap]
    _ = (-S2853ChartYNegT K) * ↑(S2853ChartYNegUnit K) := by rw [g0Ring_apply_t]
    _ = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K) := by
        rw [show S2853ChartYNegT K = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (-(S2853ChartYT K)) * ↑((S2853ChartYNegUnit K)⁻¹) from rfl]
        rw [RingHom.map_neg (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)) (S2853ChartYT K)]
        calc (-(-algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K) *
              ↑((S2853ChartYNegUnit K)⁻¹))) * ↑(S2853ChartYNegUnit K)
            = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K) *
                (↑((S2853ChartYNegUnit K)⁻¹) * ↑(S2853ChartYNegUnit K)) := by ring
          _ = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K) * 1 := by
              rw [Units.inv_mul]
          _ = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K) := by
              rw [mul_one]

/-- The second iteration of the chart-Y negation composed with the chart-Y negation
is the localization map. -/
theorem sigmaRing_comp_g0Ring :
    (sigmaRing K).comp (g0Ring K) =
      algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply]
    rw [show Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.C a) =
      algebraMap K (E37ChartYRing K) a from Ideal.Quotient.mk_algebraMap K (I := E37ChartYIdeal K) a]
    rw [g0Ring_algebraMap_K K a]
    rw [IsScalarTower.algebraMap_apply K (E37ChartYRing K) (S2853ChartYNegRing K) a]
    rw [sigmaRing_algebraMap, g0Ring_algebraMap_K K a,
      IsScalarTower.algebraMap_apply K (E37ChartYRing K) (S2853ChartYNegRing K) a]
  · intro i
    fin_cases i
    · simp only [RingHom.comp_apply]
      change sigmaRing K (g0Ring K (S2853ChartYS K)) =
        algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K)
      rw [g0Ring_apply_s, sigmaRing_negS]
    · simp only [RingHom.comp_apply]
      change sigmaRing K (g0Ring K (S2853ChartYT K)) =
        algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K)
      rw [g0Ring_apply_t, sigmaRing_negT]

/-! ## 3. The chart-Y negation is an involution at the level of schemes -/

/-- On `Spec (Away (1 + t))` the map induced by the chart-Y negation factors through
the chart-Y piece `f0`. -/
theorem sigmaRing_specMap_comp_f0 :
    Spec.map (CommRingCat.ofHom (g0Ring K)) =
      Spec.map (CommRingCat.ofHom (sigmaRing K)) ≫ f0 K := by
  rw [← specMap_comp_ringHom (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K))
    (sigmaRing K)]
  rw [sigmaRing_comp_algebraMap]

/-- Applying the chart-Y negation twice on `Spec (Away (1 + t))` is the identity. -/
theorem sigmaRing_specMap_comp_g0Ring :
    Spec.map (CommRingCat.ofHom (sigmaRing K)) ≫ Spec.map (CommRingCat.ofHom (g0Ring K)) =
      f0 K := by
  rw [← specMap_comp_ringHom (g0Ring K) (sigmaRing K)]
  rw [sigmaRing_comp_g0Ring]


/-! ## 4. The two chart-Y pieces of the square -/

/-- The `f0`-piece (`D(1 + t)`) of the square: the second iteration of the chart-Y negation
is the inclusion of the piece. -/
theorem g0Scheme_comp_globalAlpha :
    g0Scheme K ≫ globalAlphaScheme K = f0 K ≫ S2820E37ChartYMap K := by
  have hα : S2820E37ChartYMap K ≫ globalAlphaScheme K = chartYNegGlued K :=
    (D K).openCover.ι_glueMorphisms (globalAlphaComp K) (globalAlphaCompat K) (ULift.up true)
  have hf0 : f0 K ≫ chartYNegGlued K = g0Scheme K :=
    (chartYCover K).ι_glueMorphisms (chartYNegGMap K) (hf_pair K) false
  calc g0Scheme K ≫ globalAlphaScheme K
      = (Spec.map (CommRingCat.ofHom (g0Ring K)) ≫ S2820E37ChartYMap K) ≫
          globalAlphaScheme K := rfl
    _ = Spec.map (CommRingCat.ofHom (g0Ring K)) ≫
          (S2820E37ChartYMap K ≫ globalAlphaScheme K) := by rw [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (g0Ring K)) ≫ chartYNegGlued K := by rw [hα]
    _ = (Spec.map (CommRingCat.ofHom (sigmaRing K)) ≫ f0 K) ≫ chartYNegGlued K := by
        rw [sigmaRing_specMap_comp_f0]
    _ = Spec.map (CommRingCat.ofHom (sigmaRing K)) ≫ (f0 K ≫ chartYNegGlued K) := by
        rw [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (sigmaRing K)) ≫ g0Scheme K := by rw [hf0]
    _ = Spec.map (CommRingCat.ofHom (sigmaRing K)) ≫
          (Spec.map (CommRingCat.ofHom (g0Ring K)) ≫ S2820E37ChartYMap K) := rfl
    _ = (Spec.map (CommRingCat.ofHom (sigmaRing K)) ≫
          Spec.map (CommRingCat.ofHom (g0Ring K))) ≫ S2820E37ChartYMap K := by
        rw [Category.assoc]
    _ = f0 K ≫ S2820E37ChartYMap K := by rw [sigmaRing_specMap_comp_g0Ring]

/-- The `f1`-piece (`D(t)`) of the square: the chart-Z coordinates of the chart-Y
negation agree with the chart-Z negation followed by the global alpha map. -/
theorem g1Scheme_comp_globalAlpha :
    g1Scheme K ≫ globalAlphaScheme K = f1 K ≫ S2820E37ChartYMap K := by
  have hα : S2820E37ChartZMap K ≫ globalAlphaScheme K =
      S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K :=
    (D K).openCover.ι_glueMorphisms (globalAlphaComp K) (globalAlphaCompat K) (ULift.up false)
  have hg1 : Spec.map (CommRingCat.ofHom (g1Ring K)) =
      Spec.map (CommRingCat.ofHom (alpha K)) ≫ S2853ChartZSchemeEndo K := by
    rw [g1Ring_eq_alpha_chartZNeg]
    exact specMap_comp_ringHom (S2853RingHom K) (alpha K)
  have hR : f1 K ≫ S2820E37ChartYMap K =
      Spec.map (CommRingCat.ofHom (alpha K)) ≫ S2820E37ChartZMap K :=
    glue_condition_formula K
  have hcomp : Spec.map (CommRingCat.ofHom (g1Ring K)) ≫ S2853ChartZSchemeEndo K =
      Spec.map (CommRingCat.ofHom (alpha K)) := by
    rw [hg1, Category.assoc, chartZSchemeEndo_sq, Category.comp_id]
  rw [hR]
  calc g1Scheme K ≫ globalAlphaScheme K
      = (Spec.map (CommRingCat.ofHom (g1Ring K)) ≫ S2820E37ChartZMap K) ≫
          globalAlphaScheme K := rfl
    _ = Spec.map (CommRingCat.ofHom (g1Ring K)) ≫
          (S2820E37ChartZMap K ≫ globalAlphaScheme K) := by rw [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (g1Ring K)) ≫
          (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) := by rw [hα]
    _ = (Spec.map (CommRingCat.ofHom (g1Ring K)) ≫ S2853ChartZSchemeEndo K) ≫
          S2820E37ChartZMap K := by rw [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (alpha K)) ≫ S2820E37ChartZMap K := by rw [hcomp]

/-- Composing the chart-Y negation with the global alpha self-map returns the
chart-Y inclusion. -/
theorem chartYNegGlued_comp_globalAlpha :
    chartYNegGlued K ≫ globalAlphaScheme K = S2820E37ChartYMap K := by
  refine (chartYCover K).hom_ext _ _ ?_
  intro b
  cases b
  · have hf0 : f0 K ≫ chartYNegGlued K = g0Scheme K :=
      (chartYCover K).ι_glueMorphisms (chartYNegGMap K) (hf_pair K) false
    change f0 K ≫ (chartYNegGlued K ≫ globalAlphaScheme K) =
      f0 K ≫ S2820E37ChartYMap K
    rw [← Category.assoc, hf0]
    exact g0Scheme_comp_globalAlpha K
  · have hf1 : f1 K ≫ chartYNegGlued K = g1Scheme K :=
      (chartYCover K).ι_glueMorphisms (chartYNegGMap K) (hf_pair K) true
    change f1 K ≫ (chartYNegGlued K ≫ globalAlphaScheme K) =
      f1 K ≫ S2820E37ChartYMap K
    rw [← Category.assoc, hf1]
    exact g1Scheme_comp_globalAlpha K

/-! ## 5. The global alpha self-map squares to the identity -/

theorem alpha_square :
    globalAlphaScheme K ≫ globalAlphaScheme K = 𝟙 (S2820E37ProjectiveScheme K) := by
  apply (D K).openCover.hom_ext
  intro i
  cases i with
  | up b =>
    cases b
    · change S2820E37ChartZMap K ≫ (globalAlphaScheme K ≫ globalAlphaScheme K) =
        S2820E37ChartZMap K ≫ 𝟙 (S2820E37ProjectiveScheme K)
      have hZ : S2820E37ChartZMap K ≫ globalAlphaScheme K =
          S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K :=
        (D K).openCover.ι_glueMorphisms (globalAlphaComp K) (globalAlphaCompat K)
          (ULift.up false)
      calc S2820E37ChartZMap K ≫ (globalAlphaScheme K ≫ globalAlphaScheme K)
          = (S2820E37ChartZMap K ≫ globalAlphaScheme K) ≫ globalAlphaScheme K := by
            rw [Category.assoc]
        _ = (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) ≫ globalAlphaScheme K := by
            rw [hZ]
        _ = S2853ChartZSchemeEndo K ≫
              (S2820E37ChartZMap K ≫ globalAlphaScheme K) := by rw [Category.assoc]
        _ = S2853ChartZSchemeEndo K ≫
              (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) := by rw [hZ]
        _ = (S2853ChartZSchemeEndo K ≫ S2853ChartZSchemeEndo K) ≫
              S2820E37ChartZMap K := by rw [Category.assoc]
        _ = 𝟙 (S2801E37AffineScheme K) ≫ S2820E37ChartZMap K := by
            rw [chartZSchemeEndo_sq]
        _ = S2820E37ChartZMap K := by rw [Category.id_comp]
        _ = S2820E37ChartZMap K ≫ 𝟙 (S2820E37ProjectiveScheme K) := by
            rw [Category.comp_id]
    · change S2820E37ChartYMap K ≫ (globalAlphaScheme K ≫ globalAlphaScheme K) =
        S2820E37ChartYMap K ≫ 𝟙 (S2820E37ProjectiveScheme K)
      have hY : S2820E37ChartYMap K ≫ globalAlphaScheme K = chartYNegGlued K :=
        (D K).openCover.ι_glueMorphisms (globalAlphaComp K) (globalAlphaCompat K)
          (ULift.up true)
      calc S2820E37ChartYMap K ≫ (globalAlphaScheme K ≫ globalAlphaScheme K)
          = (S2820E37ChartYMap K ≫ globalAlphaScheme K) ≫ globalAlphaScheme K := by
            rw [Category.assoc]
        _ = chartYNegGlued K ≫ globalAlphaScheme K := by rw [hY]
        _ = S2820E37ChartYMap K := chartYNegGlued_comp_globalAlpha K
        _ = S2820E37ChartYMap K ≫ 𝟙 (S2820E37ProjectiveScheme K) := by
            rw [Category.comp_id]

#check chartYNegGlued_comp_globalAlpha
#check alpha_square
#print axioms alpha_square

end LeanFormal.IUT.XiFPaper.S2858AlphaSquareActual
end
