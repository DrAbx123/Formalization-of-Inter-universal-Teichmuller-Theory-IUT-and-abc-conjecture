import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual
import tmp.sheaf.xif.paper.S2832ChartZPointAtInfinityNoGoActual
import tmp.sheaf.xif.paper.S2832D6AssemblyActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2845ZeroPreimageActual

open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2832ChartZPointAtInfinityNoGoActual
open LeanFormal.IUT.XiFPaper.S2832D6AssemblyActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2831E37InfinityNotOverlapActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual

/-- Generic no-chartZ-preimage for the infinity section, for any base field. -/
theorem S2845_no_chartZ_infinity (K : Type) [Field K] :
    ¬ ∃ z : Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K,
        z ≫ S2820E37ChartZMap K =
          Spec.map (CommRingCat.ofHom (E37InfinityEval K)) ≫ S2820E37ChartYMap K := by
  rintro ⟨z, hz⟩
  let D : Scheme.GlueData := E37ProjGlueData K (S2820E37TransitionIso K)
  let p : Spec (CommRingCat.of K) := default
  have hinf : (Spec.map (CommRingCat.ofHom (E37InfinityEval K))) p = E37InfinityPoint K := by
    change PrimeSpectrum.comap (E37InfinityEval K) p = E37InfinityPoint K
    rfl
  have hzpoint := congrArg (fun f => f p) hz
  have hz' : D.ι (ULift.up false) (z p) = D.ι (ULift.up true) (E37InfinityPoint K) := by
    have hzpoint' : D.ι (ULift.up false) (z p) =
        D.ι (ULift.up true) ((Spec.map (CommRingCat.ofHom (E37InfinityEval K))) p) := by
      exact hzpoint
    rw [hinf] at hzpoint'
    exact hzpoint'
  have hrel := (Scheme.GlueData.ι_eq_iff D (ULift.up false) (ULift.up true)
    (z p) (E37InfinityPoint K)).mp hz'
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
  split_ifs with h
  · exfalso
    apply S2845_no_chartZ_infinity K
    rcases h with ⟨z, hz⟩
    exact ⟨z, hz⟩
  · rfl

def S2845ZeroPreimage : S2844ZeroPreimage :=
  ⟨S2844InfinityOver, S2845_gluedMap_infinity_eq_zero⟩

#check S2845_gluedMap_infinity_eq_zero
#check S2845ZeroPreimage
#print axioms S2845_gluedMap_infinity_eq_zero

end LeanFormal.IUT.XiFPaper.S2845ZeroPreimageActual
end
