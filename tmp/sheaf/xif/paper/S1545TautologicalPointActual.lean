import tmp.sheaf.xif.paper.S1495IsogenyKernelActual
import tmp.sheaf.xif.paper.S1534GenericPointJacobianActual

/-! # S1545: tautological point, affine coordinate match, and the kernel

S1495 supplies the actual translation-fixing `Isogeny.ker` and proves
`ker = torsionBy` from `TautologicalPointMulByInt`.  S1534 supplies
`genericPoint.toJacobian` and the exact affine-coordinate field.

This file proves the actual point-coordinate lemma

```text
mulByIntTautologicalPoint = .some (mulByIntX W n) (mulByIntY W n)
```

and hence

```text
TautologicalPointMulByInt ↔ S1534AffineCoordinatesMatch.
```

No general-n ZSMul coordinate formula (`zsmul_point_eq_smulEval`) is available
at Mathlib v4.32.2; the exact remaining first field is the affine-coordinate
match (equivalently the tautological-point identity).  No inhabitant of either
is assumed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1545TautologicalPointActual

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open TauCeti.Isogeny
open LeanFormal.IUT.XiFPaper.S1534GenericPointJacobianActual

universe u

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- The actual point-coordinate lemma: the tautological point of `[n]` is
exactly `(mulByIntX, mulByIntY)`. -/
theorem mulByIntTautologicalPoint_eq_some {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (h : EquationMulByInt W n) :
    ∃ hns : (W⁄W.FunctionField).Nonsingular (mulByIntX W n) (mulByIntY W n),
      mulByIntTautologicalPoint W hn h =
        WeierstrassCurve.Affine.Point.some (mulByIntX W n) (mulByIntY W n) hns := by
  let T : (W⁄W.FunctionField).Point := mulByIntTautologicalPoint W hn h
  have hT : T ≠ 0 := TauCeti.CoordinatePullback.tautologicalPoint_ne_zero
    (TauCeti.Isogeny.mulByIntPullback W hn h)
  have hx : WeierstrassCurve.Affine.Point.xCoord T = mulByIntX W n := by
    change WeierstrassCurve.Affine.Point.xCoord
      (TauCeti.CoordinatePullback.tautologicalPoint
        (TauCeti.Isogeny.mulByIntPullback W hn h)) = mulByIntX W n
    rw [TauCeti.CoordinatePullback.xCoord_tautologicalPoint,
      TauCeti.Isogeny.mulByIntPullback_X]
  have hy : WeierstrassCurve.Affine.Point.yCoord T = mulByIntY W n := by
    change WeierstrassCurve.Affine.Point.yCoord
      (TauCeti.CoordinatePullback.tautologicalPoint
        (TauCeti.Isogeny.mulByIntPullback W hn h)) = mulByIntY W n
    rw [TauCeti.CoordinatePullback.yCoord_tautologicalPoint,
      TauCeti.Isogeny.mulByIntPullback_Y]
  refine ⟨?_, ?_⟩
  · rw [← hx, ← hy]
    exact WeierstrassCurve.Affine.Point.nonsingular_coords hT
  · change T = WeierstrassCurve.Affine.Point.some (mulByIntX W n) (mulByIntY W n) _
    simpa only [hx, hy] using (WeierstrassCurve.Affine.Point.some_coords hT).symm

/-- The tautological-point identity is exactly the S1534 affine-coordinate
match. -/
theorem tautologicalPointMulByInt_iff_affineCoordinatesMatch {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (h : EquationMulByInt W n) :
    TautologicalPointMulByInt W hn h ↔ S1534AffineCoordinatesMatch W n := by
  constructor
  · intro htaut
    obtain ⟨hns, hT⟩ := mulByIntTautologicalPoint_eq_some W hn h
    refine ⟨hns, ?_⟩
    change n • genericPoint W = _
    rw [← htaut, hT]
  · rintro ⟨hns, hcoord⟩
    obtain ⟨hns', hT⟩ := mulByIntTautologicalPoint_eq_some W hn h
    change mulByIntTautologicalPoint W hn h = n • genericPoint W
    rw [hT, hcoord]

/-- The actual `Isogeny.ker = torsionBy` from the affine-coordinate match, via
S1495's actual translation-fixing kernel. -/
theorem ker_mulByIntIsogeny_eq_torsionBy_of_affineCoordinatesMatch [DecidableEq F] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (h : EquationMulByInt W n)
    (hm : MapsInfinityMulByInt W hn h)
    (haff : S1534AffineCoordinatesMatch W n) :
    (mulByIntIsogeny W hn h hm).ker = AddSubgroup.torsionBy (W⁄F).Point n :=
  TauCeti.Isogeny.ker_mulByIntIsogeny_eq_torsionBy W hn h hm
    ((tautologicalPointMulByInt_iff_affineCoordinatesMatch W hn h).mpr haff)

#check mulByIntTautologicalPoint_eq_some
#check tautologicalPointMulByInt_iff_affineCoordinatesMatch
#check ker_mulByIntIsogeny_eq_torsionBy_of_affineCoordinatesMatch

end LeanFormal.IUT.XiFPaper.S1545TautologicalPointActual
end
