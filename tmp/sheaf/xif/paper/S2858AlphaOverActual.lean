/-
S2858: the global chart-alpha self-map of the fixed E37 projective scheme is an
endomorphism of the D6 base-change object `S2844X = S2821AsOver K` over `Spec K`.

The point is the compatibility of `globalAlphaScheme K` with the structure map
`S2821StructureMap K`.  It is checked on the two charts of the glue data
`D K = E37ProjGlueData K (S2820E37TransitionIso K)`:

* chart Z: `S2821ChartZ_structure` identifies the structure map of the chart
  with `S2801E37StructureMap`, and the chart-Z substitution
  `(x, y) ↦ (x, -y - 1)` fixes the base field, so it fixes the structure map;
* chart Y: `chartYNegGlued K` is glued from the two chart-Y pieces
  `g0Scheme`/`g1Scheme`, and each piece fixes `K` at the level of rings
  (`g0Ring`/`g1Ring` fix `algebraMap K`), whence it also fixes the
  structure map.

Consequently `alphaOver = Over.homMk (globalAlphaScheme K) _` is an
endomorphism of `S2821AsOver K`, and `alphaOver` squares to the identity by
`Over.ext` and `S2858AlphaSquareActual.alpha_square`.
-/

import tmp.sheaf.xif.paper.S2858AlphaSquareActual
import tmp.sheaf.xif.paper.S2856HfOverlapActual
import tmp.sheaf.xif.paper.S2856HfYZRingActual
import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual
open LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
open LeanFormal.IUT.XiFPaper.S2856HfOverlapActual
open LeanFormal.IUT.XiFPaper.S2856HfYZRingActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaCompatActual
open LeanFormal.IUT.XiFPaper.S2858AlphaSquareActual
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.XiFPaper.S2858AlphaOverActual

variable (K : Type) [Field K] [DecidableEq K]

/-! ## 1. The chart-Z endomorphism fixes the structure map -/

/-- The chart-Z substitution fixes the base field: `S2853RingHom` fixes the
image of `algebraMap K` in the chart-Z coordinate ring. -/
theorem S2853RingHom_algebraMap (a : K) :
    S2853RingHom K (algebraMap K (S2801E37CoordinateRing K) a) =
      algebraMap K (S2801E37CoordinateRing K) a := by
  have h : algebraMap K (S2801E37CoordinateRing K) a =
      Ideal.Quotient.mk (S2801E37Ideal K) (MvPolynomial.C a) :=
    (Ideal.Quotient.mk_algebraMap K (I := S2801E37Ideal K) a).symm
  rw [h]
  unfold S2853RingHom S2853PolyHom
  rw [Ideal.Quotient.lift_mk]
  simp

/-- `Spec.map` of a ring map fixing `K`, composed with the structure map of
the source, is the structure map of the target. -/
theorem specMap_comp_structure {A B : Type} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    (f : A →+* B) (hf : ∀ a : K, f (algebraMap K A a) = algebraMap K B a) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  exact hf a

theorem chartZSchemeEndo_structure :
    S2853ChartZSchemeEndo K ≫ S2801E37StructureMap K = S2801E37StructureMap K := by
  unfold S2853ChartZSchemeEndo S2801E37StructureMap
  exact specMap_comp_structure K (S2853RingHom K) (S2853RingHom_algebraMap K)

/-! ## 2. The two chart-Y pieces fix the structure map -/

theorem g0Scheme_structure :
    g0Scheme K ≫ S2821StructureMap K = f0 K ≫ E37ChartYStructureMap K := by
  unfold g0Scheme f0
  rw [Category.assoc, S2821ChartY_structure K]
  rw [show E37ChartYStructureMap K =
      Spec.map (CommRingCat.ofHom (algebraMap K (E37ChartYRing K))) from rfl]
  rw [specMap_comp_structure K (g0Ring K) (g0Ring_algebraMap_K K)]
  rw [specMap_comp_structure K
    (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K))
    (fun a => (IsScalarTower.algebraMap_apply K (E37ChartYRing K)
      (S2853ChartYNegRing K) a).symm)]

theorem g1Scheme_structure :
    g1Scheme K ≫ S2821StructureMap K = f1 K ≫ E37ChartYStructureMap K := by
  unfold g1Scheme f1
  rw [Category.assoc, S2821ChartZ_structure K]
  rw [show E37ChartYStructureMap K =
      Spec.map (CommRingCat.ofHom (algebraMap K (E37ChartYRing K))) from rfl]
  rw [specMap_comp_structure K (g1Ring K) (g1Ring_algebraMap_K K)]
  rw [specMap_comp_structure K
    (algebraMap (E37ChartYRing K) (Localization.Away (tY K)))
    (fun a => (IsScalarTower.algebraMap_apply K (E37ChartYRing K)
      (Localization.Away (tY K)) a).symm)]

/-! ## 3. The chart-Y negation fixes the structure map -/

theorem chartYNegGlued_structure :
    chartYNegGlued K ≫ S2821StructureMap K =
      S2820E37ChartYMap K ≫ S2821StructureMap K := by
  rw [S2821ChartY_structure K]
  refine (chartYCover K).hom_ext _ _ ?_
  intro b
  cases b
  · have hf0 : f0 K ≫ chartYNegGlued K = g0Scheme K :=
      (chartYCover K).ι_glueMorphisms (chartYNegGMap K) (hf_pair K) false
    change f0 K ≫ (chartYNegGlued K ≫ S2821StructureMap K) =
      f0 K ≫ E37ChartYStructureMap K
    rw [← Category.assoc, hf0]
    exact g0Scheme_structure K
  · have hf1 : f1 K ≫ chartYNegGlued K = g1Scheme K :=
      (chartYCover K).ι_glueMorphisms (chartYNegGMap K) (hf_pair K) true
    change f1 K ≫ (chartYNegGlued K ≫ S2821StructureMap K) =
      f1 K ≫ E37ChartYStructureMap K
    rw [← Category.assoc, hf1]
    exact g1Scheme_structure K

/-! ## 4. The global alpha self-map fixes the structure map -/

/-- The missing compatibility `hw`: the chart-alpha self-map of the fixed E37
projective scheme is a morphism over `Spec K`. -/
theorem globalAlphaScheme_structure :
    globalAlphaScheme K ≫ S2821StructureMap K = S2821StructureMap K := by
  apply (D K).openCover.hom_ext
  intro i
  cases i with
  | up b =>
    cases b
    · change S2820E37ChartZMap K ≫ (globalAlphaScheme K ≫ S2821StructureMap K) =
        S2820E37ChartZMap K ≫ S2821StructureMap K
      have hZ : S2820E37ChartZMap K ≫ globalAlphaScheme K =
          S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K :=
        (D K).openCover.ι_glueMorphisms (globalAlphaComp K) (globalAlphaCompat K)
          (ULift.up false)
      calc S2820E37ChartZMap K ≫ (globalAlphaScheme K ≫ S2821StructureMap K)
          = (S2820E37ChartZMap K ≫ globalAlphaScheme K) ≫ S2821StructureMap K := by
            rw [Category.assoc]
        _ = (S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K) ≫ S2821StructureMap K := by
            rw [hZ]
        _ = S2853ChartZSchemeEndo K ≫ (S2820E37ChartZMap K ≫ S2821StructureMap K) := by
            rw [Category.assoc]
        _ = S2853ChartZSchemeEndo K ≫ S2801E37StructureMap K := by
            rw [S2821ChartZ_structure K]
        _ = S2801E37StructureMap K := chartZSchemeEndo_structure K
        _ = S2820E37ChartZMap K ≫ S2821StructureMap K := by
            rw [S2821ChartZ_structure K]
    · change S2820E37ChartYMap K ≫ (globalAlphaScheme K ≫ S2821StructureMap K) =
        S2820E37ChartYMap K ≫ S2821StructureMap K
      have hY : S2820E37ChartYMap K ≫ globalAlphaScheme K = chartYNegGlued K :=
        (D K).openCover.ι_glueMorphisms (globalAlphaComp K) (globalAlphaCompat K)
          (ULift.up true)
      calc S2820E37ChartYMap K ≫ (globalAlphaScheme K ≫ S2821StructureMap K)
          = (S2820E37ChartYMap K ≫ globalAlphaScheme K) ≫ S2821StructureMap K := by
            rw [Category.assoc]
        _ = chartYNegGlued K ≫ S2821StructureMap K := by rw [hY]
        _ = S2820E37ChartYMap K ≫ S2821StructureMap K := chartYNegGlued_structure K

/-! ## 5. The induced endomorphism of the D6 object -/

/-- The chart-alpha automorphism of the fixed E37 projective scheme as an
endomorphism of the D6 base-change object
`S2821AsOver K = Over.mk (S2821StructureMap K)`. -/
noncomputable def alphaOver : S2821AsOver K ⟶ S2821AsOver K :=
  Over.homMk (globalAlphaScheme K) (globalAlphaScheme_structure K)

theorem alphaOver_square :
    alphaOver K ≫ alphaOver K = 𝟙 (S2821AsOver K) := by
  apply Over.OverMorphism.ext
  change globalAlphaScheme K ≫ globalAlphaScheme K = 𝟙 (S2820E37ProjectiveScheme K)
  exact alpha_square K

/-! ## 6. Specialization to the D6 field `K = A6F6` -/

/-- The induced endomorphism of the actual D6 object
`S2844X = S2821AsOver A6F6`. -/
noncomputable def alphaOverS2844 :
    S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X := by
  classical
  exact alphaOver S2844D6F6BaseChangeActual.K

theorem alphaOverS2844_square :
    alphaOverS2844 ≫ alphaOverS2844 =
      𝟙 S2844D6F6BaseChangeActual.S2844X := by
  classical
  exact alphaOver_square S2844D6F6BaseChangeActual.K

#check alphaOver
#check alphaOver_square
#check alphaOverS2844
#check alphaOverS2844_square
#print axioms alphaOver
#print axioms alphaOver_square
#print axioms alphaOverS2844
#print axioms alphaOverS2844_square

end LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
end
