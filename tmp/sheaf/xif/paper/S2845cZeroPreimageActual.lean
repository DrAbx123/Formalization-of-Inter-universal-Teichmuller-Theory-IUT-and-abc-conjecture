import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual
import tmp.sheaf.xif.paper.S2831E37InfinityNotOverlapActual
import tmp.sheaf.xif.paper.S2820E37TransitionActual
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
import tmp.sheaf.xif.paper.S2801D6FaithfulActual
import tmp.sheaf.xif.paper.S2821E37ProjectiveOverActual
import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2845cZeroPreimageActual

open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2813E37TwoFPointsActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2831E37InfinityNotOverlapActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual

local instance : Field K := inferInstance
local instance : DecidableEq K := Classical.decEq _

noncomputable def S2845PointAtInfinityMorphism :
    Spec (CommRingCat.of K) ⟶ S2820E37ProjectiveScheme K :=
  Spec.map (CommRingCat.ofHom (E37InfinityEval K)) ≫ S2820E37ChartYMap K

theorem S2845_infinityOver_left :
    (S2844InfinityOver).left = S2845PointAtInfinityMorphism := by
  rfl

theorem S2845_no_chartZ :
    ¬ ∃ z : Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K,
        z ≫ S2820E37ChartZMap K = S2845PointAtInfinityMorphism := by
  rintro ⟨z, hz⟩
  let D : Scheme.GlueData.{0} := E37ProjGlueData K (S2820E37TransitionIso K)
  let p : Spec (CommRingCat.of K) := default
  have hinf : (Spec.map (CommRingCat.ofHom (E37InfinityEval K))) p = E37InfinityPoint K := by
    change PrimeSpectrum.comap (E37InfinityEval K) p = E37InfinityPoint K
    rfl
  have hzpoint := congrArg (fun f => f p) hz
  have hzpoint' : D.ι (ULift.up false) (z p) =
      D.ι (ULift.up true) ((Spec.map (CommRingCat.ofHom (E37InfinityEval K))) p) := by
    simpa [D, S2845PointAtInfinityMorphism, E37ProjGlueData, E37ProjF, E37ProjU,
      S2821ChartYOver] using hzpoint
  rw [hinf] at hzpoint'
  have hrel := (Scheme.GlueData.ι_eq_iff D (ULift.up false) (ULift.up true)
    (z p) (E37InfinityPoint K)).mp hzpoint'
  rcases hrel with ⟨x, hxleft, hxright⟩
  apply S2831_infinityPoint_not_mem_overlap_range K
  refine ⟨(S2820E37TransitionIso K).hom x, ?_⟩
  have hxright' : E37ChartYOverlapMap K ((S2820E37TransitionIso K).hom x) =
      E37InfinityPoint K := by
    simpa [D, E37ProjGlueData, E37ProjT, E37ProjF, E37ProjV] using hxright
  exact hxright'

theorem S2845_gluedMap_infinity_eq_zero :
    S2844GluedMap (S2844InfinityOver).left = 0 := by
  classical
  unfold S2844GluedMap
  rw [S2845_infinityOver_left]
  split_ifs with h
  · exact absurd h S2845_no_chartZ
  · rfl

theorem S2845ZeroPreimage : S2844ZeroPreimage :=
  ⟨S2844InfinityOver, S2845_gluedMap_infinity_eq_zero⟩

noncomputable def S2845CurvePointRealization :
    S2813CurvePointRealization K S2844X S2844Punctured :=
  S2844CurvePointRealization S2845ZeroPreimage

#check S2845CurvePointRealization
#check S2845ZeroPreimage
#print axioms S2845ZeroPreimage

end LeanFormal.IUT.XiFPaper.S2845cZeroPreimageActual
end
