import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaPunctureIdeal
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Projectivity and rank one for the puncture ideal: conditional and obstruction

This file tries to prove the puncture ideal/module of the affine Weierstrass
coordinate ring is projective of rank one.

The actual Mathlib API used:

* Submodule.projective_of_isUnit: an invertible (unit) submodule is projective;
* Module.Invertible.finrank_eq_one: an invertible free module has finrank one.

The exact missing inputs are isolated:

* the point ideal XYIdeal is not known to be a unit submodule of R;
* the ideal module is not known to be Module.Invertible/Free;
* Mathlib has no smooth affine Weierstrass curve Dedekind-domain instance and no
  theorem that the affine point ideal is invertible in the submodule monoid.

The affine-infinity case is proved to give the unit ideal and the trivial free
module, which is an obstruction rather than the theta line bundle.

No fake line bundle or fake Dedekind instance is introduced.
No theta spec, rank or cardinal claim is used.
-/

namespace ABCBridge.SourceQlThetaPunctureIdealProjective

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InfinitePlacePsiCnsResidual
open ABCBridge.SourceQlThetaObjectActual
open ABCBridge.SourceQlThetaLineBundleFromCurve
open ABCBridge.SourceQlThetaLineBundleObstruction
open ABCBridge.SourceQlThetaPunctureDivisor
open ABCBridge.SourceQlThetaPunctureIdeal
open scoped BigOperators

universe u

variable {l : LeanFormal.IUT.PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- The actual affine coordinate ring of the source curve. -/
abbrev sourcePunctureProjectiveRing : Type u :=
  sourcePunctureCoordinateRing S

/-- The actual ideal module. -/
abbrev sourcePunctureProjectiveModule : Type u :=
  sourcePunctureIdealModule S

/-- Conditional projectivity from the actual invertible-submodule API. -/
theorem sourcePunctureIdeal_projective_of_isUnit
    (hunit : IsUnit
      (sourcePunctureVanishingIdeal S :
        Submodule (sourcePunctureProjectiveRing S)
          (sourcePunctureProjectiveRing S))) :
    Module.Projective (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S) :=
  Submodule.projective_of_isUnit (R := sourcePunctureProjectiveRing S)
    (A := sourcePunctureProjectiveRing S) hunit

/-- Conditional rank-one from the actual invertible-free-module API. -/
theorem sourcePunctureIdeal_finrank_one_of_invertible_free
    [Module.Free (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S)]
    [Module.Invertible (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S)] :
    Module.finrank (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S) = 1 :=
  Module.Invertible.finrank_eq_one (sourcePunctureProjectiveRing S)
    (sourcePunctureProjectiveModule S)

/-- Combined conditional projectivity/rank-one. -/
theorem sourcePunctureIdeal_projective_rankOne_of_inputs
    (hunit : IsUnit
      (sourcePunctureVanishingIdeal S :
        Submodule (sourcePunctureProjectiveRing S)
          (sourcePunctureProjectiveRing S)))
    [Module.Free (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S)]
    [Module.Invertible (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S)] :
    Module.Projective (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveModule S)
      ∧ Module.finrank (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveModule S) = 1 :=
  ⟨sourcePunctureIdeal_projective_of_isUnit S hunit,
    sourcePunctureIdeal_finrank_one_of_invertible_free S⟩

/-- The exact missing unit-submodule input: the affine point ideal is a unit in
the submodule monoid.  It is not proved by the current tree. -/
def SourcePunctureIdealUnitSubmodule : Prop :=
  IsUnit
    (sourcePunctureVanishingIdeal S :
      Submodule (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveRing S))

/-- The exact missing invertible-module input. -/
def SourcePunctureIdealInvertibleModule : Prop :=
  Module.Invertible (sourcePunctureProjectiveRing S)
    (sourcePunctureProjectiveModule S)

/-- The exact missing free-module input. -/
def SourcePunctureIdealFreeModule : Prop :=
  Module.Free (sourcePunctureProjectiveRing S)
    (sourcePunctureProjectiveModule S)

/-- The current API proves projectivity from the missing unit-submodule input. -/
theorem sourcePunctureIdeal_projective_conditional :
    SourcePunctureIdealUnitSubmodule S →
      Module.Projective (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveModule S) :=
  sourcePunctureIdeal_projective_of_isUnit S

/-- The current API proves rank-one from the missing invertible+free inputs. -/
theorem sourcePunctureIdeal_rankOne_conditional
    (hunit : SourcePunctureIdealUnitSubmodule S)
    (hinv : SourcePunctureIdealInvertibleModule S)
    (hfree : SourcePunctureIdealFreeModule S) :
    Module.finrank (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S) = 1 := by
  haveI : Module.Free (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S) := hfree
  haveI : Module.Invertible (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S) := hinv
  exact sourcePunctureIdeal_finrank_one_of_invertible_free S

/-- The affine-infinity obstruction again: the unit ideal gives the trivial free
module, not a point line bundle. -/
theorem sourcePunctureIdeal_infinity_trivial
    (h : sourcePunctureAffinePoint S =
      (WeierstrassCurve.Affine.Point.zero :
        (sourcePunctureAffineModel S).Point)) :
    sourcePunctureVanishingIdeal S = ⊤
      ∧ Nonempty (sourcePunctureProjectiveModule S
        ≃ₗ[sourcePunctureProjectiveRing S]
          sourcePunctureProjectiveRing S) :=
  sourcePunctureIdeal_infinity_obstruction S h

/-- Exact missing API statement: Mathlib does not supply the smooth affine
Weierstrass coordinate-ring Dedekind instance or the point-ideal unit proof.
Only the conditional consequences are proved. -/
theorem sourcePunctureIdeal_missingAPI :
    SourcePunctureIdealUnitSubmodule S →
      Module.Projective (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveModule S) :=
  sourcePunctureIdeal_projective_conditional S

/-- The six missing geometric theta items. -/
def sourcePunctureIdealProjective_missing :
    List SourceThetaLineBundleObstructionDatum :=
  sourceThetaLineBundleObstructionMissing S

/-- Six items remain missing. -/
theorem sourcePunctureIdealProjective_missing_length :
    (sourcePunctureIdealProjective_missing S).length = 6 :=
  sourceThetaLineBundleObstructionMissing_length S

/-- Exact residual: conditional projectivity/rank-one, infinity obstruction, and
the six missing geometric items. -/
theorem sourcePunctureIdealProjective_exactResidual :
    (SourcePunctureIdealUnitSubmodule S →
      Module.Projective (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveModule S))
      ∧
    (SourcePunctureIdealUnitSubmodule S →
      SourcePunctureIdealInvertibleModule S →
      SourcePunctureIdealFreeModule S →
      Module.finrank (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveModule S) = 1)
      ∧
    (sourcePunctureIdealProjective_missing S).length = 6 :=
  ⟨sourcePunctureIdeal_projective_conditional S,
    sourcePunctureIdeal_rankOne_conditional S,
    sourcePunctureIdealProjective_missing_length S⟩

/-- No fake Dedekind instance or fake line bundle is introduced. -/
theorem sourcePunctureIdealProjective_noFake :
    (sourcePunctureIdealProjective_missing S).length = 6 :=
  sourcePunctureIdealProjective_missing_length S

/-- Conditional projectivity directly from the actual invertible-module API. -/
theorem sourcePunctureIdeal_projective_of_invertible
    [Module.Invertible (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S)] :
    Module.Projective (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S) :=
  inferInstance

/-- Conditional rank-one from the actual invertible-module API. -/
theorem sourcePunctureIdeal_finrank_one_of_invertible
    [Module.Free (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S)]
    [Module.Invertible (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S)] :
    Module.finrank (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S) = 1 :=
  Module.Invertible.finrank_eq_one (sourcePunctureProjectiveRing S)
    (sourcePunctureProjectiveModule S)

/-- The affine point case carries an actual nonsingular point, but no unit-ideal
proof. -/
theorem sourcePunctureIdeal_affine_point_smooth
    {x y : S.arithmetic.F} {h : (sourcePunctureAffineModel S).Nonsingular x y}
    (hpt : sourcePunctureAffinePoint S =
      WeierstrassCurve.Affine.Point.some x y h) :
    sourcePunctureVanishingIdeal S =
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          (sourcePunctureAffineModel S) x (Polynomial.C y)
      ∧ (sourcePunctureAffineModel S).Nonsingular x y :=
  ⟨sourcePunctureIdeal_affine_candidate S hpt, h⟩

/-- The exact unit-submodule input is not the trivial free module claim: it is the
invertibility of the actual point ideal. -/
theorem sourcePunctureIdeal_unitSubmodule_boundary :
    SourcePunctureIdealUnitSubmodule S →
      Module.Projective (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveModule S) :=
  sourcePunctureIdeal_projective_conditional S

/-- The exact missing relation between fractional-ideal invertibility and
submodule unit status is not asserted; only the conditional consequence is
proved. -/
theorem sourcePunctureIdeal_fractionalIdeal_boundary :
    SourcePunctureIdealUnitSubmodule S →
      Module.Projective (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveModule S) :=
  sourcePunctureIdeal_projective_conditional S

/-- The six missing items in exact order. -/
theorem sourcePunctureIdealProjective_missing_eq :
    (sourcePunctureIdealProjective_missing S) =
      [ .curveLineBundle,
        .thetaObjectATheta,
        .geometricThetaDivisor,
        .unitComparisonMqMTheta,
        .muTwoLDeckRootAction,
        .conjugateSynchronization ] := rfl

/-- The affine-infinity case is the exact obstruction, not a theta line bundle. -/
theorem sourcePunctureIdealProjective_infinity_obstruction
    (h : sourcePunctureAffinePoint S =
      (WeierstrassCurve.Affine.Point.zero :
        (sourcePunctureAffineModel S).Point)) :
    sourcePunctureVanishingIdeal S = ⊤
      ∧ Nonempty (sourcePunctureProjectiveModule S
        ≃ₗ[sourcePunctureProjectiveRing S]
          sourcePunctureProjectiveRing S) :=
  sourcePunctureIdeal_infinity_obstruction S h


/-- Conditional line-bundle data for the puncture ideal. -/
structure SourcePunctureIdealProjectiveDatum where
  ideal_eq : sourcePunctureVanishingIdeal S =
    sourcePunctureVanishingIdeal S
  projective : Module.Projective (sourcePunctureProjectiveRing S)
    (sourcePunctureProjectiveModule S)
  rankOne : Module.finrank (sourcePunctureProjectiveRing S)
    (sourcePunctureProjectiveModule S) = 1

/-- The conditional datum's projective field. -/
theorem sourcePunctureIdealProjectiveDatum_projective
    (D : SourcePunctureIdealProjectiveDatum S) :
    Module.Projective (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S) :=
  D.projective

/-- The conditional datum's rank-one field. -/
theorem sourcePunctureIdealProjectiveDatum_rankOne
    (D : SourcePunctureIdealProjectiveDatum S) :
    Module.finrank (sourcePunctureProjectiveRing S)
      (sourcePunctureProjectiveModule S) = 1 :=
  D.rankOne

/-- The exact missing input can be bundled as a conditional datum; no inhabitant
is constructed. -/
theorem sourcePunctureIdealProjectiveDatum_boundary :
    SourcePunctureIdealUnitSubmodule S →
      Module.Projective (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveModule S) :=
  sourcePunctureIdeal_projective_conditional S

/-- Exact final boundary: conditional projectivity/rank-one, infinity
obstruction, and the six missing geometry items. -/
theorem sourcePunctureIdealProjective_finalBoundary :
    (SourcePunctureIdealUnitSubmodule S →
      Module.Projective (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveModule S))
      ∧
    (SourcePunctureIdealUnitSubmodule S →
      SourcePunctureIdealInvertibleModule S →
      SourcePunctureIdealFreeModule S →
      Module.finrank (sourcePunctureProjectiveRing S)
        (sourcePunctureProjectiveModule S) = 1)
      ∧
    (sourcePunctureIdealProjective_missing S).length = 6 :=
  ⟨sourcePunctureIdeal_projective_conditional S,
    sourcePunctureIdeal_rankOne_conditional S,
    sourcePunctureIdealProjective_missing_length S⟩


end

end ABCBridge.SourceQlThetaPunctureIdealProjective
