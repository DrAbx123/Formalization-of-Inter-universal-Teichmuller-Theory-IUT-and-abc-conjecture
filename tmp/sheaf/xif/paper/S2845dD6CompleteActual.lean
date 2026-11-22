import tmp.sheaf.xif.paper.S2845cZeroPreimageActual
import tmp.sheaf.xif.paper.S2846D6F6MissingActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility
import Mathlib.AlgebraicGeometry.OpenImmersion

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2845dD6CompleteActual

open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2845cZeroPreimageActual
open LeanFormal.IUT.XiFPaper.S2846D6F6MissingActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

local instance : Field K := inferInstance
local instance : DecidableEq K := Classical.decEq _

theorem S2845d_two_chartZ_over_points :
    ∃ f g : S2844Base ⟶ S2844X, f ≠ g := by
  have h0 : (0 : K) ^ 2 + 0 = (0 : K) ^ 3 - 0 := by ring
  have h1 : (-1 : K) ^ 2 + (-1) = (0 : K) ^ 3 - 0 := by ring
  refine ⟨S2844ChartZOver 0 0 h0, S2844ChartZOver 0 (-1) h1, ?_⟩
  intro hEq
  have hleft := congrArg Over.Hom.left hEq
  change E37ChartZSchemePoint K 0 0 h0 ≫ S2820E37ChartZMap K =
    E37ChartZSchemePoint K 0 (-1) h1 ≫ S2820E37ChartZMap K at hleft
  haveI : IsOpenImmersion (S2820E37ChartZMap K) :=
    (E37ProjGlueData K (S2820E37TransitionIso K)).ι_isOpenImmersion (ULift.up false)
  haveI : Mono (S2820E37ChartZMap K) :=
    IsOpenImmersion.mono (S2820E37ChartZMap K)
  have hp : E37ChartZSchemePoint K 0 0 h0 =
      E37ChartZSchemePoint K 0 (-1) h1 :=
    (cancel_mono (S2820E37ChartZMap K)).mp hleft
  have hring := congrArg
    (Spec.homEquiv (R := CommRingCat.of (S2801E37CoordinateRing K))
      (S := CommRingCat.of K)) hp
  have hy := congrArg (fun f : CommRingCat.of (S2801E37CoordinateRing K) ⟶
      CommRingCat.of K => f.hom (S2801E37Y K)) hring
  simp only [E37ChartZSchemePoint, Spec.homEquiv_apply, Spec.preimage_map,
    CommRingCat.hom_ofHom, E37ChartZPoint_Y] at hy
  norm_num at hy

theorem S2845d_not_pointFiber : ¬ IsPointFiber (S2844Fiber) := by
  rintro hp
  obtain ⟨f, g, hfg⟩ := S2845d_two_chartZ_over_points
  have hsub : Subsingleton
      ((S2844Fiber).obj (LocallyDiscrete.mk (Opposite.op (baseSchemeObject K)))) :=
    hp (Opposite.op (baseSchemeObject K))
  change Subsingleton (Discrete (S2844Base ⟶ S2844X)) at hsub
  haveI := hsub
  have hEq : (Discrete.mk f : Discrete (S2844Base ⟶ S2844X)) = Discrete.mk g :=
    Subsingleton.elim _ _
  exact hfg (Discrete.mk.injEq _ _ |>.mp hEq)

noncomputable def S2845dD6Complete : MissingD6GeometricRealization K :=
  S2846D6 S2845ZeroPreimage S2845d_not_pointFiber

#check S2845dD6Complete
#print axioms S2845dD6Complete

end LeanFormal.IUT.XiFPaper.S2845dD6CompleteActual
end
