import tmp.sheaf.xif.paper.S2482CoordRingEquivActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482NormTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482CoordRingEquivActual
open Polynomial

noncomputable def S2482BaseMap : Polynomial F →+* S2482CoordinateRing :=
  (S2482CoordRingEquiv : S2482W.CoordinateRing →+* S2482CoordinateRing).comp
    (algebraMap (Polynomial F) S2482W.CoordinateRing)

noncomputable instance S2482ModulePolynomial :
    Module (Polynomial F) S2482CoordinateRing :=
  Module.compHom S2482CoordinateRing S2482BaseMap

noncomputable instance S2482AlgebraPolynomial :
    Algebra (Polynomial F) S2482CoordinateRing :=
  Algebra.ofModule'
    (by
      intro r x
      rw [RingHom.toModule_smul]
      rw [show r • x = S2482BaseMap r * x from rfl]
      ring)
    (by
      intro r x
      rw [RingHom.toModule_smul]
      rw [show r • x = S2482BaseMap r * x from rfl]
      ring)

noncomputable def S2482LinearMap :
    S2482W.CoordinateRing →ₗ[Polynomial F] S2482CoordinateRing where
  toFun := S2482CoordRingEquiv
  map_add' := map_add _
  map_smul' c x := by
    rw [Algebra.smul_def, map_mul]
    congr 1

noncomputable def S2482LinearEquiv :
    S2482W.CoordinateRing ≃ₗ[Polynomial F] S2482CoordinateRing :=
  LinearEquiv.ofBijective S2482LinearMap S2482CoordRingEquiv.bijective

noncomputable def S2482Basis :
    Module.Basis (Fin 2) (Polynomial F) S2482CoordinateRing :=
  (WeierstrassCurve.Affine.CoordinateRing.basis S2482W).map S2482LinearEquiv


theorem S2482_algebraMap_eq (r : Polynomial F) :
    algebraMap (Polynomial F) S2482CoordinateRing r = S2482BaseMap r := by
  rw [Algebra.algebraMap_eq_smul_one]
  rw [show r • (1 : S2482CoordinateRing) = S2482BaseMap r * 1 from rfl]
  simp

theorem S2482CoordRingEquiv_algebraMap (r : Polynomial F) :
    S2482CoordRingEquiv
      (algebraMap (Polynomial F) S2482W.CoordinateRing r) =
      algebraMap (Polynomial F) S2482CoordinateRing r := by
  have h1 : r • (1 : S2482CoordinateRing) = S2482BaseMap r := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact S2482_algebraMap_eq r
  have hW : r • (1 : S2482W.CoordinateRing) =
      algebraMap (Polynomial F) S2482W.CoordinateRing r :=
    (Algebra.algebraMap_eq_smul_one r).symm
  rw [← hW, S2482_algebraMap_eq, ← h1]
  have h := S2482LinearMap.map_smul' r (1 : S2482W.CoordinateRing)
  simpa [S2482LinearMap] using h

end LeanFormal.IUT.XiFPaper.S2482NormTransportActual

end