/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual
import tmp.sheaf.xif.paper.S1906RankTwoTorsionActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual

/-!
# S2511: naturality of the projective--affine comparison under the actual
Galois action

Let `E' = S1720Curve` be the actual punctured elliptic curve over the actual
number field `F' = S1720Field`, let `K` be an algebraic closure of `F'`, and let
`W = E'_K = S1906W` be the base change.  The actual absolute Galois group
`Gal(K/F') = S1725AbsoluteGalois` acts on the projective points `W.Point`
through

`S1720Curve.galoisActionOnPoint : Gal(K/F') -> W.Point ->+ W.Point`

and on the affine points through

`S2056PointMap : Gal(K/F') -> W.Point ->+ W.Point`.

The projective--affine comparison

`S1906ProjAffineEquiv : W.Point ~= W.Point`

is the Mathlib additive equivalence
`WeierstrassCurve.Projective.Point.toAffineAddEquiv W`.

## Main result

`S2511ProjAffineEquiv_galoisActionOnPoint`:

  `S1906ProjAffineEquiv (galoisActionOnPoint sigma P) =
     S2056PointMap sigma (S1906ProjAffineEquiv P)`

for every `sigma : Gal(K/F')` and every projective point `P`.  Thus the
comparison is equivariant for the two actual actions.

The proof does not need a case split on the point at infinity: the actual
action `galoisActionOnPoint` is *defined* by conjugating the affine point map
`S2056PointMap` by `toAffineAddEquiv`, so the naturality is a definitional
identity.  The point-at-infinity case is recorded separately in
`S2511ProjAffineEquiv_galoisActionOnPoint_zero`.

## Matrix form

Over a chosen `ZMod l`-basis `b` of the actual `l`-torsion, the matrix
representation acts by the Galois action on torsion points
(`S1894MatrixRep_acts`).  Combining this with the naturality shows that the
affine point attached to the matrix-transported torsion point `b (rho v)` is
the `S2056PointMap`-image of the affine point attached to `b v`
(`S2511MatrixRep_affine`).

No `sorry`, `admit`, `axiom`, `True`, `PUnit` or `native_decide` is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2511AffineNaturalityActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual

/-! ## 1. Naturality of the comparison -/

/-- **Naturality of the projective--affine comparison under the actual Galois
action.**  For every `sigma` in the absolute Galois group and every projective
point `P` of `W = E'_K`, transporting the `sigma`-image of `P` to affine
coordinates is the same as applying the affine point map `S2056PointMap sigma`
to the affine point attached to `P`. -/
theorem S2511ProjAffineEquiv_galoisActionOnPoint
    (sigma : S1725AbsoluteGalois)
    (P : WeierstrassCurve.Projective.Point S1906W) :
    S1906ProjAffineEquiv (S1720Curve.galoisActionOnPoint sigma P) =
      S2056PointMap sigma (S1906ProjAffineEquiv P) := by
  rw [PuncturedEllipticCurve.galoisActionOnPoint]
  unfold S2056PointMap S1906ProjAffineEquiv
  simpa only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    AddMonoidHom.comp_apply, Function.comp_apply, AddEquiv.apply_symm_apply]

/-- The same naturality with both sides written in terms of the Mathlib
projective--affine equivalence and the affine point map. -/
theorem S2511ToAffine_galoisActionOnPoint
    (sigma : S1725AbsoluteGalois)
    (P : WeierstrassCurve.Projective.Point S1906W) :
    WeierstrassCurve.Projective.Point.toAffineAddEquiv S1906W
        (S1720Curve.galoisActionOnPoint sigma P) =
      WeierstrassCurve.Affine.Point.map (W' := S1720Curve.curve) sigma.toAlgHom
        (WeierstrassCurve.Projective.Point.toAffineAddEquiv S1906W P) :=
  S2511ProjAffineEquiv_galoisActionOnPoint sigma P

/-! ## 2. The point at infinity -/

/-- The point at infinity is the zero of the projective point group, and the
projective--affine comparison sends it to the affine zero. -/
theorem S2511ProjAffineEquiv_zero :
    S1906ProjAffineEquiv (0 : WeierstrassCurve.Projective.Point S1906W) = 0 :=
  map_zero S1906ProjAffineEquiv

/-- The naturality square at the point at infinity: the projective point at
infinity is fixed by the actual Galois action and both sides are the affine
zero. -/
theorem S2511ProjAffineEquiv_galoisActionOnPoint_zero
    (sigma : S1725AbsoluteGalois) :
    S1906ProjAffineEquiv
        (S1720Curve.galoisActionOnPoint sigma
          (0 : WeierstrassCurve.Projective.Point S1906W)) =
      S2056PointMap sigma
        (S1906ProjAffineEquiv (0 : WeierstrassCurve.Projective.Point S1906W)) :=
  S2511ProjAffineEquiv_galoisActionOnPoint sigma 0

/-! ## 3. Matrix form on the actual `l`-torsion -/

/-- **Matrix form of the naturality.**  For a chosen rank-two `ZMod l`-basis `b`
of the actual `l`-torsion `E'[l]`, the affine point attached to the
matrix-transported torsion point `b (rho_{l,b}(sigma) v)` is the
`sigma`-image, under `S2056PointMap`, of the affine point attached to `b v`.
This is the composite of `S1894MatrixRep_acts` (the matrix acts through the
actual Galois action on torsion points) with the naturality of the
projective--affine comparison. -/
theorem S2511MatrixRep_affine (l : PrimeGeFive) (b : S1725TorsionBasis l)
    (sigma : S1725AbsoluteGalois) (v : Fin 2 → ZMod l.value) :
    S1906ProjAffineEquiv
        (b ((Matrix.GeneralLinearGroup.toLin
          (S1720Curve.galoisLTorsionMatrixRepresentation l b sigma)).toLinearEquiv v) :
            WeierstrassCurve.Projective.Point S1906W) =
      S2056PointMap sigma
        (S1906ProjAffineEquiv
          (b v : WeierstrassCurve.Projective.Point S1906W)) := by
  rw [S1894MatrixRep_acts l b sigma v]
  rw [PuncturedEllipticCurve.galoisActionOnLTorsionLinearEquiv_apply]
  rw [PuncturedEllipticCurve.galoisActionOnLTorsion_coe]
  exact S2511ProjAffineEquiv_galoisActionOnPoint sigma
    (b v : WeierstrassCurve.Projective.Point S1906W)

/-! ## 4. Axiom footprint -/

#print axioms S2511ProjAffineEquiv_galoisActionOnPoint
#print axioms S2511ToAffine_galoisActionOnPoint
#print axioms S2511ProjAffineEquiv_zero
#print axioms S2511ProjAffineEquiv_galoisActionOnPoint_zero
#print axioms S2511MatrixRep_affine

end LeanFormal.IUT.XiFPaper.S2511AffineNaturalityActual

end
