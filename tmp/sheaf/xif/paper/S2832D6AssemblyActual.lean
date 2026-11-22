import tmp.sheaf.xif.paper.S2812IsStackActual
import tmp.sheaf.xif.paper.S2802D6FiberActual
import tmp.sheaf.xif.paper.S2831GluedOverPointMapActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2832D6AssemblyActual

open LeanFormal.IUT.XiFPaper.S2802D6FiberActual
open LeanFormal.IUT.XiFPaper.S2812IsStackActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.XiFPaper.S2830GluedPointMapActual
open LeanFormal.IUT.XiFPaper.S2831GluedOverPointMapActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2829E37GaussianPointActual
open LeanFormal.IUT.XiFPaper.S2813E37TwoFPointsActual
open LeanFormal.IUT.XiFPaper.S2789E37OrbicurveSignActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

local instance : Field K := S2789Arithmetic.fieldF
local instance : DecidableEq K := Classical.decEq _

noncomputable def S2832PuncturedCurve : PuncturedEllipticCurve K where
  curve := S2829Curve
  isElliptic := S2829_isElliptic
  puncture := 0

noncomputable abbrev S2832Fiber : Iut.EtaleStackPseudofunctor K :=
  S2802Fiber K (S2821AsOver K)

noncomputable def S2832MissingD6
    (hnon : ¬ IsPointFiber (S2832Fiber))
    (hsurj : Function.Surjective (fun P :
      (Iut.schemeRepresentableEtalePseudofunctor K (S2821AsOver K)).obj
        (LocallyDiscrete.mk (Opposite.op (baseSchemeObject K))) =>
      S2830GluedMap (Over.Hom.left P.as))) :
    MissingD6GeometricRealization K where
  curve := S2832PuncturedCurve
  fiber := S2832Fiber
  isStack :=
    S2812IsStackActual.schemeRepresentableEtalePseudofunctor_isStack K
      (S2821AsOver K)
  nondegenerate := hnon
  curvePointRealization :=
    ⟨fun (P : (Iut.schemeRepresentableEtalePseudofunctor K (S2821AsOver K)).obj
        (LocallyDiscrete.mk (Opposite.op (baseSchemeObject K)))) =>
      S2830GluedMap (Over.Hom.left P.as), hsurj⟩

#check S2832PuncturedCurve
#check S2832Fiber
#check S2832MissingD6
#print axioms S2832MissingD6


theorem S2832_not_pointFiber_of_two_distinct
    (h2 : ∃ f g : S2813Base K ⟶ S2821AsOver K, f ≠ g) :
    ¬ IsPointFiber (S2832Fiber) := by
  rintro hpoint
  obtain ⟨f, g, hfg⟩ := h2
  have hsub : Subsingleton
      ((S2832Fiber).obj (LocallyDiscrete.mk (Opposite.op (baseSchemeObject K)))) :=
    hpoint (Opposite.op (baseSchemeObject K))
  change Subsingleton (Discrete (S2813Base K ⟶ S2821AsOver K)) at hsub
  haveI := hsub
  have hEq : (Discrete.mk f : Discrete (S2813Base K ⟶ S2821AsOver K)) =
      Discrete.mk g := Subsingleton.elim _ _
  exact hfg (Discrete.mk.injEq _ _ |>.mp hEq)

#check S2832_not_pointFiber_of_two_distinct


theorem S2832_two_chartZ_over_points :
    ∃ f g : S2813Base K ⟶ S2821AsOver K, f ≠ g := by
  have h0 : (0 : K) ^ 2 + 0 = (0 : K) ^ 3 - 0 := by ring
  have h1 : (-1 : K) ^ 2 + (-1) = (0 : K) ^ 3 - 0 := by ring
  refine ⟨S2831ChartZOverPoint 0 0 h0, S2831ChartZOverPoint 0 (-1) h1, ?_⟩
  intro hEq
  have hleft := congrArg Over.Hom.left hEq
  change E37ChartZSchemePoint K 0 0 h0 ≫ S2820E37ChartZMap K =
    E37ChartZSchemePoint K 0 (-1) h1 ≫ S2820E37ChartZMap K at hleft
  haveI : IsOpenImmersion (S2820E37ChartZMap K) :=
    (E37ProjGlueData K (S2820E37TransitionIso K)).ι_isOpenImmersion (ULift.up false)
  haveI : Mono (S2820E37ChartZMap K) :=
    IsOpenImmersion.mono (S2820E37ChartZMap K)
  have hp : E37ChartZSchemePoint K 0 0 h0 = E37ChartZSchemePoint K 0 (-1) h1 :=
    (cancel_mono (S2820E37ChartZMap K)).mp hleft
  have hring := congrArg
    (Spec.homEquiv (R := CommRingCat.of (S2801E37CoordinateRing K))
      (S := CommRingCat.of K)) hp
  have hy := congrArg (fun f : CommRingCat.of (S2801E37CoordinateRing K) ⟶
      CommRingCat.of K => f.hom (S2801E37Y K)) hring
  simp only [E37ChartZSchemePoint, Spec.homEquiv_apply, Spec.preimage_map,
    CommRingCat.hom_ofHom, E37ChartZPoint_Y] at hy
  norm_num at hy

#check S2832_two_chartZ_over_points
#print axioms S2832_two_chartZ_over_points


theorem S2832_not_pointFiber : ¬ IsPointFiber (S2832Fiber) := by
  apply S2832_not_pointFiber_of_two_distinct
  exact S2832_two_chartZ_over_points

#check S2832_not_pointFiber
#print axioms S2832_not_pointFiber

end LeanFormal.IUT.XiFPaper.S2832D6AssemblyActual
end
