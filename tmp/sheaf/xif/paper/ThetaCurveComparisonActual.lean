import tmp.sheaf.xif.paper.ThetaQuotientTotalActual
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMap

/-!
# Actual analytic/Tate curve comparison map

Intermediate construction: the actual theta period root r (r^2 = q) is used as
the Tate parameter for the actual Tate Weierstrass curve

  weierstrassCurve L r.

On the actual pole-excluded parameter domain coordinateParameterDomain r, the
actual Tate coordinate maps tateWeierstrassX r u and tateWeierstrassY r u give a
map to the affine coordinates of that curve:

  thetaTateCoordinateMap D u = (tateWeierstrassX D.r u, tateWeierstrassY D.r u).

The coordinates are invariant under the actual r^Z period action
u ↦ r^a u, so the map factors through the actual Tate parameter quotient
TateParameterQuotient D.r D.r_ne_zero.

This is a genuine intermediate analytic/Tate comparison map. It does not
construct a line-bundle isomorphism with the source curve and does not assert
the unproved nonsingularity/equation point data; no donor is used. No inequality
is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ABCBridge.ThetaCurveComparisonActual

open LeanFormal.IUT.Foundations.Theta
open LeanFormal.IUT.TateCurve

universe u

/-- The actual Tate coordinate map on the pole-excluded domain. -/
def thetaTateCoordinateMap {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (u : ↥(coordinateParameterDomain D.r)) : L × L :=
  (tateWeierstrassX D.r (u : L), tateWeierstrassY D.r (u : L))

/-- The coordinate map is invariant under the actual r^Z action. -/
theorem thetaTateCoordinateMap_orbit
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (a : ℤ) (u : ↥(coordinateParameterDomain D.r)) :
    thetaTateCoordinateMap D
        ⟨D.r ^ a * (u : L),
          (coordinateParameterDomain_zpow_mul_parameter D.r_ne_zero a (u : L)).mpr u.2⟩ =
      thetaTateCoordinateMap D u := by
  ext
  · simp [thetaTateCoordinateMap,
      tateWeierstrassX_zpow_mul_parameter D.r_ne_zero a (u : L)]
  · simp [thetaTateCoordinateMap,
      tateWeierstrassY_zpow_mul_parameter D.r_ne_zero a (u : L)]

/-- The actual comparison map on the Tate parameter quotient. -/
noncomputable def thetaTateQuotientCoordinateMap
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) :
    TateParameterQuotient D.r D.r_ne_zero → L × L :=
  Quotient.lift
    (fun u : ↥(coordinateParameterDomain D.r) => thetaTateCoordinateMap D u)
    (by
      intro u v huv
      rcases huv with ⟨a, ha⟩
      -- the quotient relation is v = r^a * u in the parameter
      have h := thetaTateCoordinateMap_orbit D a u
      rw [ha] at h
      exact h.symm)

/-- Value of the quotient comparison map on a representative. -/
theorem thetaTateQuotientCoordinateMap_mk
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (u : ↥(coordinateParameterDomain D.r)) :
    thetaTateQuotientCoordinateMap D (Quotient.mk _ u) =
      thetaTateCoordinateMap D u :=
  rfl

/-- The actual Tate curve used by the intermediate comparison. -/
abbrev thetaTateCurve {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) : WeierstrassCurve L :=
  weierstrassCurve L D.r

/-- The actual parameter used by the Tate curve. -/
theorem thetaTateCurve_parameter
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) :
    thetaTateCurve D = weierstrassCurve L D.r := rfl

end ABCBridge.ThetaCurveComparisonActual

end
