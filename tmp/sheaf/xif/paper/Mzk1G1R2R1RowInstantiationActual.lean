/- R2 per-row V(p,j,t) and R1 rows instantiated from the DONE actual theta coefficient rows.

  `Mzk1G1F2ThetaCoeffRowActual` supplies, for each Bad place b and signed label j, the
  actual qVFam row coefficients `thetaCoeffRow T b j : qVFamTensorV -> R` (equal to the
  DONE alignment coefficients).  Here:
  * R1 row: `thetaR1Row T b j := thetaCoeffRow T b j ()` (the actual coefficient scalar),
  * R2 per-row V: `thetaRowV T b j0 j et := sum_i thetaCoeffRow T b j0 (et i)` for an
    ordered tuple `et : Fin (j+1) -> qVFamTensorV`, and the weighted-average bound
    obtained by feeding it to the DONE `stepV_weightedAverage_le_of_distinguished`.
  No new analytic input; the row bound remains an explicit hypothesis.
  No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaCoeffRowActual
import tmp.sheaf.xif.paper.Mzk1BoxStepVAverageActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R2R1RowInstantiationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaCoeffRowActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxStepVAverageActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.IUTIV.StepVProcessionAverage

instance qVFamTensorVFintype : Fintype qVFamTensorV := inferInstanceAs (Fintype Unit)
instance qVFamTensorVNonempty : Nonempty qVFamTensorV := inferInstanceAs (Nonempty Unit)

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **R1 row（实际标量）**：Bad 位 b、标签 j 的实际 theta 系数。 -/
noncomputable def thetaR1Row (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) : ℝ :=
  thetaCoeffRow T b j ()

theorem thetaR1Row_eq_alignment (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    thetaR1Row T b j = (thetaTensorQVFamAlignmentOfActual T).coefficients j b := rfl

/-- **R2 per-row V(p,j,t)**：有序 tuple 上实际 theta 系数行之和。 -/
noncomputable def thetaRowV (b : Bad (nativePlaceSelection T))
    (j0 : SignedLabel l.value) (j : ℕ) (et : Fin (j + 1) → qVFamTensorV) : ℝ :=
  ∑ i : Fin (j + 1), thetaCoeffRow T b j0 (et i)

/-- R2 的加权平均界：由 DONE 的 distinguished-slot 平均定理直接实例化。 -/
theorem thetaRowV_weightedAverage_le
    (b : Bad (nativePlaceSelection T)) (j0 : SignedLabel l.value)
    (lam : qVFamTensorV → ℝ) (hlam : ∀ e, 0 < lam e)
    (logp iotaL : ℝ) (lrep : (l.value : ℝ) ≠ 0) (j : ℕ)
    (d oq : qVFamTensorV → ℝ) (slot : Fin (j + 1))
    (bound : ∀ et : Fin (j + 1) → qVFamTensorV,
      thetaRowV T b j0 j et ≤ collectionChoiceBound (l.value : ℝ) logp iotaL j d oq et slot) :
    (∑ et : Fin (j + 1) → qVFamTensorV,
        thetaRowV T b j0 j et * ∏ i, lam (et i)) /
      (∑ et : Fin (j + 1) → qVFamTensorV, ∏ i, lam (et i)) ≤
      collectionBound (l.value : ℝ)
        ((∑ e, d e * logp * lam e) / ∑ e, lam e)
        ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j :=
  stepV_weightedAverage_le_of_distinguished lam hlam (l.value : ℝ) logp iotaL lrep
    j d oq slot (thetaRowV T b j0 j) bound

#print axioms thetaR1Row_eq_alignment
#print axioms thetaRowV_weightedAverage_le

end LeanFormal.IUT.XiFPaper.Mzk1G1R2R1RowInstantiationActual