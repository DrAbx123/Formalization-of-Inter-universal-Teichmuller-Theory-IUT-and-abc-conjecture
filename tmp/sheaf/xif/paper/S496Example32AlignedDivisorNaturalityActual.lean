import tmp.sheaf.xif.paper.S492Example32InputActual
import tmp.sheaf.xif.paper.S468DivisorNaturalityActual
import tmp.sheaf.xif.paper.S481AlignedDivisorMapActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S496Example32AlignedDivisorNaturalityActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open LeanFormal.IUT.XiFPaper.S481AlignedDivisorMapActual
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

theorem phi_gpPullback_id {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    (example32PhiIsFSM K).gpPullback f =
      AddMonoidHom.id (Algebra.GrothendieckAddGroup
        ((example32PhiIsFSM K).obj Y).carrier) := by
  apply Algebra.GrothendieckAddGroup.lift.symm.injective
  apply AddMonoidHom.ext
  intro value
  rw [Algebra.GrothendieckAddGroup.lift_symm_apply]
  let map := Algebra.GrothendieckAddGroup.of.comp
    (AddMonoidHom.id ((example32PhiIsFSM K).obj Y).carrier)
  change (Algebra.GrothendieckAddGroup.lift map)
    (Algebra.GrothendieckAddGroup.of value) = map value
  change ((Algebra.GrothendieckAddGroup.lift map).comp
    Algebra.GrothendieckAddGroup.of) value = map value
  rw [← Algebra.GrothendieckAddGroup.lift_symm_apply]
  exact DFunLike.congr_fun
    (Equiv.symm_apply_apply Algebra.GrothendieckAddGroup.lift map) value

theorem liftedPullback_ofMul_up {X Y : Example32SmallBase K} (f : X ⟶ Y)
    (u : (coverField Y)ˣ) :
    (example32RationalFunctionsLiftedULift (K := K)).pullback f
        (Additive.ofMul (ULift.up u)) =
      Additive.ofMul (ULift.up (unitInclusionPullback f u)) := rfl

/-- Exact missing evaluation lemma: aligned divisor on a ULifted unit equals the
Grothendieck image of the unaligned divisor.  Its proof is blocked by the
current instance transparency of `example32AlignedDivisor`'s local `letI`. -/
def example32AlignedDivisorEvalGap : Prop :=
  ∀ (V : DvSmallValuationFamily (K := K)) (Z : Example32SmallBase K)
    (z : (coverField Z)ˣ),
    example32AlignedDivisor (K := K) V Z
        (Additive.ofMul (ULift.up z)) =
      grothendieckStageDivisorULift
        (divisorMap (V Z) (Additive.ofMul z))

def example32AlignedDivisorNaturalityGap : Prop :=
  ∀ (V : DvSmallValuationFamily (K := K))
    (hV : DvSmallValuationCompatibility (K := K) V)
    {X Y : Example32SmallBase K} (f : X ⟶ Y)
    (value : (example32RationalFunctionsLiftedULift (K := K)).obj Y),
    example32AlignedDivisor (K := K) V X
        ((example32RationalFunctionsLiftedULift (K := K)).pullback f value) =
      (example32PhiIsFSM K).gpPullback f
        (example32AlignedDivisor (K := K) V Y value)

end LeanFormal.IUT.XiFPaper.S496Example32AlignedDivisorNaturalityActual

end
