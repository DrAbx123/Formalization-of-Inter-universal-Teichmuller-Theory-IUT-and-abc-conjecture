/- G1-A (h) M-g sub-step A: the base-changed lambda chart -> overlap open immersion.
   Four-part reuse: (1) old corpus: overlapToChart0 + tensor facts; no conclusions reused;
   (2) accepted: IsLocalization.tensorProduct_tensorProduct (BaseChange.lean:363);
   (3) Mathlib: Algebra.TensorProduct.map, IsLocalization.Away, IsOpenImmersion.of_isLocalization;
   (4) ADAPTER. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapKbarActual
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Polynomial MvPolynomial
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatGeomIntegralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothGeomIntegralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapKbarActual

abbrev K : Type := FermatK

/-- 张量化后的 chart0 → overlap 环同态。 -/
noncomputable def chart0ToOverlapK (n : Nat) :
    Chart0Ring n ⊗[ℚ] K →+* Overlap0 n ⊗[ℚ] K :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (Chart0Ring n) (Overlap0 n))
    (AlgHom.id ℚ K)).toRingHom

#print axioms chart0ToOverlapK
/- HANDOFF (M-g O1/O3): `chart0ToOverlapK` is green.  The Algebra/IsScalarTower instances for the
   tensorized overlap map repeatedly hit instance-defeq stalls (`Algebra ?m ?m` stuck, `algebraMap`
   elaborated with a different CommSemiring path).  Recommended next attempt (fresh context):
   (i) avoid `algebraMap` entirely: define
       `leftK : Chart0Ring n →+* Chart0Ring n (x)[Q] kbar := Algebra.TensorProduct.includeLeftRingHom`;
       `overlapKAlg := (chart0ToOverlapK n).toAlgebra`;
       `overlapKAlgR := ((chart0ToOverlapK n).comp leftK).toAlgebra`;
   (ii) prove tower pointwise by `RingHom.ext fun a => by simp [overlapKAlg, overlapKAlgR,
        chart0ToOverlapK, Algebra.TensorProduct.map, Algebra.TensorProduct.includeLeftRingHom,
        Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.includeRight_apply]`
        (do NOT expect `rfl`; expect a few `show`/`change` rounds);
   (iii) alternatively skip IsScalarTower: instantiate `IsLocalization.tensorProduct_tensorProduct`
        with a locally provided `letI : IsScalarTower ...`, or take the `IsLocalization.Away` route
        via `IsLocalization.Away.tensorProductEquivTMulRight` and transport the open-immersion
        instance along the resulting AlgEquiv (`IsOpenImmersion.of_iso`-style). -/
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatGeomIntegralActual