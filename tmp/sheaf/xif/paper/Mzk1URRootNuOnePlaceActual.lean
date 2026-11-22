/- R1: q-pilot mass via the accepted tensor-block lemma, with the paper 1/(2l) normalization.

DECISION (Lead, 2026-11-18): use the q-lattice mass route instead of a general element scaling.
Paper IV L1359-1364 DEFINES the q-pilot log as (1/(2l)) log q (normalization), not as a root element:
 q_P5 := -M_paper_v2, and the q-lattice mass is computed directly from q (no 2l-th root extraction).

Contents:
 * qLatticeMass (cP) (hq : ||q_b|| = p^(-cP)) : the accepted tensor-block mass lemma
   (arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator) applied to the
   one-place tensor block of qVFamTensorPlaces with generator = sourceRootQUnit and coefficient cP
   gives nu(q O) = -(sum_i cP) log p = -cP log p;
 * qPilotMass : the paper q-pilot normalized mass = (1/(2l)) * mass;
 * qPilotMass_eq : qPilotMass cP = -(cP/(2l)) log p.
No general norm scaling is claimed; no local_haar_modulus obligation.
-/
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Mzk1URRootExtensionActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Pointwise
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1URRootNuOnePlaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The q-lattice mass on the one-place qVFamily block, from the accepted tensor-block lemma. -/
theorem qLatticeMass
    [MeasurableSpace (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)]
    [BorelSpace (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)]
    (cP : ℝ)
    (hq : ‖(sourceRootQUnit T b : rootBase T b)‖ =
      ((qVFamTensorP T b : ℝ)) ^ (-cP)) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        MeasureTheory.Measure.addHaar
        (((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
              (fun _ => cP) *
            arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
              Submodule ℤ_[qVFamTensorP T b]
                (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)) :
          Set (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple))) =
      -cP * Real.log (qVFamTensorP T b : ℝ) := by
  have hdata := arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator
    (qVFamTensorPlaces T b) qVFamTensorTuple MeasureTheory.Measure.addHaar
    (c := fun _ => cP) (g := fun _ => (sourceRootQUnit T b : rootBase T b))
    (fun _ => hq)
  rw [hdata]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, nsmul_eq_mul]
  norm_num

/-- The paper q-pilot normalized mass: (1/(2l)) times the q-lattice mass (IV L1359-1364). -/
noncomputable def qPilotMass (cP : ℝ) : ℝ :=
  (1 / (2 * (l.value : ℝ))) * (-cP * Real.log (qVFamTensorP T b : ℝ))

/-- qPilotMass cP = -(cP/(2l)) log p. -/
theorem qPilotMass_eq (cP : ℝ) :
    qPilotMass (T := T) (b := b) cP =
      -(cP / (2 * (l.value : ℝ))) * Real.log (qVFamTensorP T b : ℝ) := by
  unfold qPilotMass
  ring

#print axioms qLatticeMass
#print axioms qPilotMass_eq


/-- From c_P = localNormOrder p q (and q nonzero), the norm of q is p^{-c_P}: this is the input
hq consumed by qLatticeMass. -/
theorem norm_eq_rpow_of_localNormOrder
    (q : rootBase T b) (hq0 : q ≠ 0) (cP : ℝ) (p : ℕ) (hp : (1 : ℝ) < (p : ℝ))
    (h : LocalFieldLogarithm.localNormOrder p q = cP) :
    ‖q‖ = (p : ℝ) ^ (-cP) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp).ne'
  have hnormpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hlog : Real.log ‖q‖ = -cP * Real.log (p : ℝ) := by
    have hh := h
    unfold LocalFieldLogarithm.localNormOrder at hh
    field_simp [hlogp] at hh
    linarith
  have hlogr : Real.log ‖q‖ = Real.log ((p : ℝ) ^ (-cP)) := by
    rw [hlog, Real.log_rpow hp0]
  exact Real.log_injOn_pos hnormpos (Real.rpow_pos_of_pos hp0 _) hlogr

#print axioms norm_eq_rpow_of_localNormOrder

end LeanFormal.IUT.XiFPaper.Mzk1URRootNuOnePlaceActual
end