/- R2 lambda supply: the actual theta generator `urRootTheta j` realizes the slot order
  `lambda = (gaussExponent j/(2l)) * badPlaceCoeff`; with `gaussExponent j = j^2` this is
  the slot coefficient `(j^2/(2l)) * oq` with `oq = badPlaceCoeff`, so the inequality
  `slot <= lambda` needed by the R2 bridge holds (even with equality, but only `<=` used).

  `localNormOrder_pow_gen` is already DONE in `Mzk1URRootExtensionActual`; the base order
  bridge `urRootTheta_order_base` is DONE there as well.
  No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1URRootExtensionActual
import tmp.sheaf.xif.paper.Mzk1URBadPlaceActualMapActual
import tmp.sheaf.xif.paper.Mzk1G1F2R2PerRowSupplyActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LambdaSupplyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1URBadPlaceActualMapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2R2PerRowSupplyActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual theta generator slot order `lambda`. -/
noncomputable def lambdaActual (j : SignedLabel l.value) : ℝ :=
  localNormOrder (qVFamTensorP T b) (urRootTheta T b j)

/-- **lambda identity**: `lambda = (gaussExponent j/(2l)) * badPlaceCoeff`. -/
theorem lambdaActual_eq (j : SignedLabel l.value) :
    lambdaActual T b j =
      ((gaussExponent j.1 : ℝ) / (2 * (l.value : ℝ))) *
        badPlaceCoeff (T := T) (b := b) := by
  unfold lambdaActual
  rw [urRootTheta_order_base]
  congr 1
  unfold Mzk1URBadPlaceActualMapActual.badPlaceCoeff
  rfl

/-- **slot <= lambda** for `oq = badPlaceCoeff`, using `gaussExponent j = j^2`.
    (Only the inequality is needed by the R2 bridge.) -/
theorem slot_le_lambdaActual (j : SignedLabel l.value)
    (hgauss : (gaussExponent j.1 : ℝ) = (j.1 : ℝ) ^ 2) :
    ((j.1 : ℝ) ^ 2 / (2 * (l.value : ℝ))) * badPlaceCoeff (T := T) (b := b) ≤
      lambdaActual T b j := by
  rw [lambdaActual_eq]
  rw [← hgauss]
  exact le_rfl

/-- **Combination with `lambdaFromQ_ge_slot`**: the arithmetic slot bound
    `(j^2/(2l)) oq <= j^2 oq` (R2PerRowSupplyActual) is compatible with the actual
    generator order; here recorded for `oq = badPlaceCoeff`. -/
theorem slot_le_lambdaFromQ (j : SignedLabel l.value)
    (hcP : 0 ≤ badPlaceCoeff (T := T) (b := b)) :
    ((j.1 : ℝ) ^ 2 / (2 * (l.value : ℝ))) * badPlaceCoeff (T := T) (b := b) ≤
      lambdaFromQ (badPlaceCoeff (T := T) (b := b)) (j.1.toNat) :=
  lambdaFromQ_ge_slot (badPlaceCoeff (T := T) (b := b)) (j.1.toNat) l hcP


/-- **q-power order identity** (Lead request): the actual sourceRootQUnit power has order
(gaussExponent j) * badPlaceCoeff, by multiplicativity of localNormOrder under integer powers. -/
theorem localNormOrder_sourceRootQUnit_zpow (j : SignedLabel l.value) :
    localNormOrder (qVFamTensorP T b)
        ((sourceRootQUnit T b : rootBase T b) ^ (gaussExponent j.1)) =
      (gaussExponent j.1 : ℝ) * badPlaceCoeff (T := T) (b := b) := by
  rw [localNormOrder_zpow_gen (qVFamTensorP T b) (gaussExponent j.1)
    (sourceRootQUnit T b : rootBase T b)
    (by exact_mod_cast Units.ne_zero (sourceRootQUnit T b))]
  unfold Mzk1URBadPlaceActualMapActual.badPlaceCoeff
  rfl

#print axioms localNormOrder_sourceRootQUnit_zpow
#print axioms lambdaActual_eq
#print axioms slot_le_lambdaActual
#print axioms slot_le_lambdaFromQ

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LambdaSupplyActual