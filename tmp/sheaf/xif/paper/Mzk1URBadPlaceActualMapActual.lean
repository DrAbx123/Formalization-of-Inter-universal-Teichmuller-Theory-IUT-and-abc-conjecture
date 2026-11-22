/- R1: actual bad-place map from the q-lattice J_b (NOT a renamed Theta) toward the actual Theta hull.

Design (Lead 2026-11-18 strategic ruling):
 * J_b := the actual q-lattice region in the one-place qVFam tensor block:
     fractionalLattice(cP_b) * holomorphicLattice,  cP_b = localNormOrder p (sourceRootQUnit_b)
   (the paper 2l-th root q-pilot; the 1/(2l) normalization enters ONCE in the log-volume comparison);
 * badPlaceQRegion_nu proves the ACTUAL normalized log volume nu(J_b) = -cP_b * log p_b using the
   DONE accepted mass lemma (qLatticeMass) and norm_eq_rpow_of_localNormOrder; J_b is NOT defined to
   be Theta and no Theta volume is assumed;
 * badPlaceActualMap_remaining is the named OPEN: the actual source-action map sigma_b carrying the
   q-lattice onto the source label-one region inside the actual Theta hull, TOGETHER with the
   measure comparison nu(sigma_b J_b) = nu(J_b).  Route: real lattice-filter determinant
   multiplicativity or mod pi^N fiber counting; a union<=average argument is explicitly excluded.
 * badPlace_chain_of_map assembles -M = sum_b w_b nu(J_b) <= nu(Theta_paper) <= H_procession from the
   map OPEN plus the existing DONE hull lower bound; no fake.
-/
import tmp.sheaf.xif.paper.Mzk1URRootNuOnePlaceActual
import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerBoundActual
import tmp.sheaf.xif.paper.Mzk1ULOrdFiberTowerActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1URBadPlaceActualMapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerBoundActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootNuOnePlaceActual
open LeanFormal.IUT.XiFPaper.Mzk1ULOrdFiberTowerActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)]

/-- The actual q-lattice coefficient at b: the normalized order of the actual q generator
(c_P = localNormOrder p q, the R0.1 caliber; no extra /e). -/
noncomputable def badPlaceCoeff : ℝ :=
  LocalFieldLogarithm.localNormOrder (qVFamTensorP T b)
    (sourceRootQUnit T b : rootBase T b)

/-- The norm input for the accepted mass lemma, from the R0.1 caliber. -/
theorem badPlaceCoeff_norm :
    ‖(sourceRootQUnit T b : rootBase T b)‖ =
      ((qVFamTensorP T b : ℝ)) ^ (-badPlaceCoeff (T := T) (b := b)) := by
  have hq0 : (sourceRootQUnit T b : rootBase T b) ≠ 0 := by
    exact_mod_cast Units.ne_zero (sourceRootQUnit T b)
  have hp : (1 : ℝ) < (qVFamTensorP T b : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
  exact norm_eq_rpow_of_localNormOrder
    (T := T) (b := b) (q := (sourceRootQUnit T b : rootBase T b))
    hq0 (badPlaceCoeff (T := T) (b := b)) (qVFamTensorP T b) hp rfl

/-- The ACTUAL q-lattice region J_b (paper 2l-th root q-pilot as a fractional lattice in the
qVFam tensor block). This is a genuine q-lattice; it is NOT a renamed Theta region. -/
noncomputable def badPlaceQRegion :
    Set (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple) :=
  (((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun _ => badPlaceCoeff (T := T) (b := b)) *
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
        Submodule ℤ_[qVFamTensorP T b]
          (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)) :
    Set (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)))

/-- ACTUAL normalized log volume of J_b (no Theta renaming; computed by the accepted mass lemma). -/
theorem badPlaceQRegion_nu :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        MeasureTheory.Measure.addHaar (badPlaceQRegion (T := T) (b := b)) =
      -badPlaceCoeff (T := T) (b := b) * Real.log (qVFamTensorP T b : ℝ) :=
  qLatticeMass (T := T) (b := b) (badPlaceCoeff (T := T) (b := b))
    (badPlaceCoeff_norm (T := T) (b := b))

/- MISSING DONOR (reported, not stubbed): the actual source-action map sigma_b.

Required objects that are NOT in the tree (verified by grep over tmp/sheaf/xif/paper):
 1. an actual map  sigma : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple -> ksBlock T b
    induced by the actual place correspondence (F-place of the qVFam block -> ksPlace T b).
    The tree contains NO construction of a function into ksBlock; the only ksBlock maps are
    self-algebra-equivalences taking an explicit algebra-equivalence input e : ksBlock T b -> ksBlock T b
    (Mzk1URPacketActualInstanceActual.lean:141, :212, :241), i.e. they presuppose such an e.
 2. a Haar pushforward comparison for that map:  (Measure.map sigma addHaar) = (local degree) * addHaar
    which is needed for nu(sigma '' J_b) = nu(J_b); no such donor exists either.
Route to build it: real lattice-filter determinant multiplicativity (associated graded of the tensor
block) or mod pi^N fiber counting; a union<=average argument is excluded (Z_p/pZ_p).
Until 1+2 exist, nu(J_b) (badPlaceQRegion_nu, PROVED) cannot be compared with nu(ksThetaHull).
-/


#print axioms badPlaceCoeff_norm
#print axioms badPlaceQRegion_nu

end LeanFormal.IUT.XiFPaper.Mzk1URBadPlaceActualMapActual
end