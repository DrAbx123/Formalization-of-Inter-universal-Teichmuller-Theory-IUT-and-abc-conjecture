import tmp.sheaf.xif.paper.S2857GlobalAlphaCompatActual
import tmp.sheaf.xif.paper.S2857GlobalAlphaActual
import tmp.sheaf.xif.paper.S2858AlphaOverActual
import tmp.sheaf.xif.paper.S2856HfYZRingActual
import tmp.sheaf.xif.paper.S2814E37ChartPointsActual

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
open LeanFormal.IUT.XiFPaper.S2856HfOverlapActual
open LeanFormal.IUT.XiFPaper.S2856HfYZRingActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaCompatActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual
open LeanFormal.IUT.XiFPaper.S2814bE37ChartZOverActual
open scoped SpecOfNotation
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2876NontrivialAlphaActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

abbrev K : Type := S2844D6F6BaseChangeActual.K
local instance : Field K := inferInstance
local instance : NumberField K := LeanFormal.IUT.XiFPaper.S2809E6FiniteActual.S2809_numberField
local instance : DecidableEq K := Classical.decEq _

theorem S2876_zero_satisfies : (0 : K) ^ 2 + 0 = 0 ^ 3 - 0 := by norm_num

theorem S2876_chartZEndo_ne_id :
    S2853ChartZSchemeEndo K ≠
      (𝟙 (S2801E37AffineScheme K) :
        S2801E37AffineScheme K ⟶ S2801E37AffineScheme K) := by
  intro h
  have hringCat : CommRingCat.ofHom (S2853RingHom K) =
      (𝟙 (CommRingCat.of (S2801E37CoordinateRing K)) :
        CommRingCat.of (S2801E37CoordinateRing K) ⟶
          CommRingCat.of (S2801E37CoordinateRing K)) := by
    apply Spec.map_injective
    simpa [S2853ChartZSchemeEndo, Spec.map_id] using h
  have hring : S2853RingHom K = RingHom.id (S2801E37CoordinateRing K) := by
    have := congrArg (fun f => f.hom) hringCat
    simpa [CommRingCat.hom_ofHom] using this
  have hY : (- S2801E37Y K - 1) = S2801E37Y K := by
    have := congrArg (fun f : S2801E37CoordinateRing K →+* S2801E37CoordinateRing K =>
      f (S2801E37Y K)) hring
    simpa [chartZ_Y] using this
  have := congrArg (E37ChartZPoint K 0 0 S2876_zero_satisfies) hY
  simpa [E37ChartZPoint_Y] using this

theorem S2876_globalAlphaScheme_ne_id :
    globalAlphaScheme K ≠
      (𝟙 (S2820E37ProjectiveScheme K) :
        S2820E37ProjectiveScheme K ⟶ S2820E37ProjectiveScheme K) := by
  intro h
  have hchart : S2820E37ChartZMap K ≫ globalAlphaScheme K =
      S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K := by
    have hf : S2820E37ChartZMap K =
        (E37ProjGlueData K (S2820E37TransitionIso K)).openCover.f
          (ULift.up false) := rfl
    have hg : globalAlphaScheme K =
        (E37ProjGlueData K (S2820E37TransitionIso K)).openCover.glueMorphisms
          (globalAlphaComp K) (globalAlphaCompat K) := rfl
    rw [hf, hg]
    have hglue :=
      (E37ProjGlueData K (S2820E37TransitionIso K)).openCover.ι_glueMorphisms
        (globalAlphaComp K) (globalAlphaCompat K) (ULift.up false)
    rw [show globalAlphaComp K (ULift.up false) =
        S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K from rfl] at hglue
    rw [← hf] at hglue ⊢
    exact hglue
  have hchart' : S2820E37ChartZMap K =
      S2853ChartZSchemeEndo K ≫ S2820E37ChartZMap K := by
    simpa [h] using hchart
  haveI : Mono (S2820E37ChartZMap K) := chartZMap_mono K
  have hendo : S2853ChartZSchemeEndo K =
      (𝟙 (S2801E37AffineScheme K) :
        S2801E37AffineScheme K ⟶ S2801E37AffineScheme K) := by
    apply (cancel_mono (S2820E37ChartZMap K)).mp
    simpa [Category.id_comp] using hchart'.symm
  exact S2876_chartZEndo_ne_id hendo

theorem S2876_alphaOverS2844_ne_id :
    alphaOverS2844 ≠
      (𝟙 S2844D6F6BaseChangeActual.S2844X) := by
  intro h
  have hleft : globalAlphaScheme K =
      (𝟙 (S2820E37ProjectiveScheme K) :
        S2820E37ProjectiveScheme K ⟶ S2820E37ProjectiveScheme K) := by
    have h' := congrArg (fun f : S2844D6F6BaseChangeActual.S2844X ⟶
      S2844D6F6BaseChangeActual.S2844X => f.left) h
    change globalAlphaScheme K = 𝟙 (S2820E37ProjectiveScheme K) at h'
    exact h'
  exact S2876_globalAlphaScheme_ne_id hleft

#check S2876_chartZEndo_ne_id
#check S2876_globalAlphaScheme_ne_id
#check S2876_alphaOverS2844_ne_id
#print axioms S2876_chartZEndo_ne_id
#print axioms S2876_globalAlphaScheme_ne_id
#print axioms S2876_alphaOverS2844_ne_id

end LeanFormal.IUT.XiFPaper.S2876NontrivialAlphaActual
end
