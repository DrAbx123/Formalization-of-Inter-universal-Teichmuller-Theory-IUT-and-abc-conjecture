/- G1-A route 2.4 exit item (h), step 1: kbar base change of the lambda chart ring.
   Step 1a: ambientEquiv A (x) kbar = kbar[X0,X1] (green 17:59:05).
   Step 1b: quotient identification (Chart n) (x) kbar = kbar[X0,X1]/(F) and IsDomain transport;
   reuses our route-new Mzk1G1FermatSmoothGeomIntegralActual.fermatCurveRing_isDomain.
   No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatSmoothGeomIntegralActual
import tmp.sheaf.xif.paper.Mzk1G1FermatAffineChartActual
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Polynomial MvPolynomial TensorProduct
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ChartKbarActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothGeomIntegralActual

abbrev K : Type := FermatK

noncomputable def ambientEquiv : A ⊗[ℚ] K ≃ₐ[ℚ] MvPolynomial (Fin 2) K :=
  (Algebra.TensorProduct.comm (R := ℚ) (A := A) (B := K)).trans
    ((MvPolynomial.algebraTensorAlgEquiv (R := ℚ) (A := K) (σ := Fin 2)).restrictScalars ℚ)

theorem ambientEquiv_algebraMap_apply (p : A) :
    ambientEquiv (algebraMap A (A ⊗[ℚ] K) p) = MvPolynomial.map (algebraMap ℚ K) p := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [ambientEquiv, Algebra.TensorProduct.comm_tmul,
    MvPolynomial.algebraTensorAlgEquiv_tmul]

theorem ambientEquiv_comp_algebraMap :
    ((ambientEquiv : A ⊗[ℚ] K →+* MvPolynomial (Fin 2) K)).comp
        (algebraMap A (A ⊗[ℚ] K))
      = MvPolynomial.map (algebraMap ℚ K) :=
  RingHom.ext ambientEquiv_algebraMap_apply

theorem map_fermatEquation_eq (n : Nat) :
    MvPolynomial.map (algebraMap ℚ K) (fermatEquation n) = fermatCurvePoly n := by
  simp [fermatEquation, fermatCurvePoly]

theorem map_fermatIdeal_eq (n : Nat) :
    Ideal.map (MvPolynomial.map (algebraMap ℚ K)) (Ideal.span {fermatEquation n})
      = fermatCurveIdeal n := by
  rw [Ideal.map_span, Set.image_singleton, map_fermatEquation_eq]
  rfl

noncomputable def chartKbarEquiv (n : Nat) :
    Mzk1G1FermatAffineChartActual.R n ⊗[ℚ] K ≃ₐ[ℚ] fermatCurveRing n := by
  refine (Algebra.TensorProduct.quotientTensorEquiv (R := ℚ) (S := ℚ) (A := A) (T := K)
    (I := Ideal.span {fermatEquation n})).trans ?_
  refine Ideal.quotientEquivAlg _ _ ambientEquiv ?_
  rw [Ideal.map_map, ambientEquiv_comp_algebraMap, map_fermatIdeal_eq]

theorem chartKbar_isDomain (n : Nat) (hn : 0 < n) :
    IsDomain (Mzk1G1FermatAffineChartActual.R n ⊗[ℚ] K) :=
  (chartKbarEquiv n).toRingEquiv.isDomain_iff.mpr (fermatCurveRing_isDomain n hn)

#print axioms ambientEquiv_comp_algebraMap
#print axioms map_fermatIdeal_eq
#print axioms chartKbar_isDomain

end LeanFormal.IUT.XiFPaper.Mzk1G1ChartKbarActual
