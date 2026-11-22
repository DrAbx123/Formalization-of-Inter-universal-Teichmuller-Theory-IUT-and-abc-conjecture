/- R1 final (container via the q-lattice, no ceiling): kurt.

Lead ruling 2026-11-18 (cheaper route): formalize the container theta side via the q-lattice in the
qVFamTensorBlock first.  Paper theta-pilot values are q_v^{j^2}, i.e. powers of q (not a root r), and
the paper normalization |log q| = (1/(2l)) log q (IV L1359-1364) is applied AFTER the q-lattice mass.
Hence:
 * thetaContainerRegion cP := the q-lattice region with coefficient cP in the one-place qVFamTensor
   block (the same object as the qLatticeMass lattice);
 * thetaContainerMass cP := (1/(2l)) * nu(thetaContainerRegion cP) = -(cP/(2l)) log p
   (the qLatticeMass donor gives nu = -cP log p; the 1/(2l) is the paper normalization);
 * container_sum_eq_neg_Mpaper: under the R0.2 crosswalk cPFullFiber_b = thetaLamWeight_b * cP_local_b,
   Sum_b thetaLamWeight_b * thetaContainerMass(cP_local_b) = -M_paper_v2 (EQUALITY, using david's
   MpaperB = -qPilotMass and M_paper_v2 = Sum MpaperB);
 * negM_le_thetaContainer: the target -M <= theta holds with equality.

Explicit input: the R0.2 crosswalk (sophie Mzk1ULR02CrosswalkActual skeleton), NOT a hidden ceiling.
K-side ksThetaHullLogRoot_lam remains a separate upper-bound proxy (ceiling discrepancy = R1 K-side
secondary open, to be absorbed by R2/exceptional).
-/
import tmp.sheaf.xif.paper.Mzk1ULOrdFiberTowerActual
import tmp.sheaf.xif.paper.Mzk1ULQbVecActual
import tmp.sheaf.xif.paper.Mzk1ULR1CPrimeFiberActual
import tmp.sheaf.xif.paper.Mzk1ULR1FiberPrimeFActual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import tmp.sheaf.xif.paper.Mzk1HT82UnderIntGenQVActual
import tmp.sheaf.xif.paper.Mzk1HT82CompletionPrimeResidueActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaContainerP5Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open NumberField
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULOrdFiberTowerActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82UnderIntGenQVActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82CompletionPrimeResidueActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The container theta region: the q-lattice region with coefficient cP in the qVFam block.
Same object as the lattice in qLatticeMass; the paper theta-pilot is the q-power family. -/
noncomputable def thetaContainerRegion (cP : ℝ) :
    Set (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple) :=
  (((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun _ => cP) *
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
        Submodule ℤ_[qVFamTensorP T b]
          (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)) :
    Set (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)))

/-- The container theta mass: (1/(2l)) * nu(q-lattice), the paper q-pilot normalization. -/
noncomputable def thetaContainerMass (cP : ℝ) : ℝ :=
  (1 / (2 * (l.value : ℝ))) * (-cP * Real.log (qVFamTensorP T b : ℝ))

/-- thetaContainerMass cP = -(cP/(2l)) log p. -/
theorem thetaContainerMass_eq (cP : ℝ) :
    thetaContainerMass (T := T) (b := b) cP =
      -(cP / (2 * (l.value : ℝ))) * Real.log (qVFamTensorP T b : ℝ) := by
  unfold thetaContainerMass
  ring

/-- Container theta sum equals -M_paper_v2, under the R0.2 crosswalk and the per-b MpaperB expansion
(explicit input hMb; david's R1CPrimeFiber lemma will discharge it). -/
theorem container_sum_eq_neg_Mpaper
    (cP_local : Bad (nativePlaceSelection T) → ℝ)
    (hcross : ∀ b : Bad (nativePlaceSelection T),
      Mzk1ULR1CPrimeFiberActual.cPFullFiber  T b = thetaLamWeight  T b * cP_local b)
    (hMb : ∀ b : Bad (nativePlaceSelection T),
      MpaperB  T b =
        (Mzk1ULR1CPrimeFiberActual.cPFullFiber  T b / (2 * (l.value : ℝ))) *
          Real.log (qVFamTensorP T b : ℝ)) :
    (∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight  T b *
          thetaContainerMass (T := T) (b := b) (cP_local b)) =
      -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2  T := by
  rw [Mzk1ULOrdFiberTowerActual.M_paper_v2_eq_sum_MpaperB  T]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [thetaContainerMass_eq, hMb b, hcross b]
  ring

/-- R1 target in the container caliber: -M_paper_v2 <= container theta sum (equality). -/
theorem negM_le_thetaContainer (cP_local : Bad (nativePlaceSelection T) → ℝ)
    (hcross : ∀ b : Bad (nativePlaceSelection T),
      Mzk1ULR1CPrimeFiberActual.cPFullFiber  T b = thetaLamWeight  T b * cP_local b)
    (hMb : ∀ b : Bad (nativePlaceSelection T),
      MpaperB  T b =
        (Mzk1ULR1CPrimeFiberActual.cPFullFiber  T b / (2 * (l.value : ℝ))) *
          Real.log (qVFamTensorP T b : ℝ)) :
    -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2  T ≤
      ∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight  T b *
          thetaContainerMass (T := T) (b := b) (cP_local b) := by
  exact le_of_eq (container_sum_eq_neg_Mpaper  T cP_local hcross hMb).symm

#print axioms thetaContainerMass_eq
#print axioms container_sum_eq_neg_Mpaper
#print axioms negM_le_thetaContainer


/-- The paper full-fiber coefficient (local copy; same formula as david's CPrimeFiber). -/
noncomputable def cPFullFiberLoc (b : Bad (nativePlaceSelection T)) : ℝ :=
  (1 / (Module.finrank ℚ (T.arithmetic.F) : ℝ)) *
    ∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      ((x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ))

/-- Per-b MpaperB expansion, discharged by the DONE FiberPrimeF theorem. -/
theorem MpaperB_eq_cPFullFiberLoc_mul_logp (b : Bad (nativePlaceSelection T)) :
    MpaperB  T b =
      (cPFullFiberLoc  T b / (2 * (l.value : ℝ))) *
        Real.log (qVFamTensorP T b : ℝ) := by
  unfold MpaperB cPFullFiberLoc
  have hlog : ∀ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      Real.log ((underIntGen (T.arithmetic.F) x.1).natAbs : ℝ) =
        Real.log (qVFamTensorP T b : ℝ) := by
    intro x hx
    rw [Mzk1ULR1FiberPrimeFActual.fiber_prime_consistency_F (T := T) b (by simpa using hx)]
  rw [Finset.sum_congr rfl (fun x hx => by rw [hlog x hx])]
  rw [← Finset.sum_mul]
  ring

#print axioms MpaperB_eq_cPFullFiberLoc_mul_logp

/-- The local full-fiber coefficient coincides with david's CPrimeFiber definition. -/
theorem cPFullFiberLoc_eq (b : Bad (nativePlaceSelection T)) :
    cPFullFiberLoc (T := T) b = Mzk1ULR1CPrimeFiberActual.cPFullFiber (T := T) b := rfl

/-- Container theta sum equals -M_paper_v2, with NO hMb input (hMb discharged by david's
fiber_prime_consistency_F); the only explicit input is the R0.2 crosswalk interface. -/
theorem container_sum_eq_neg_Mpaper_unconditional
    (cP_local : Bad (nativePlaceSelection T) → ℝ)
    (hcross : ∀ b : Bad (nativePlaceSelection T),
      Mzk1ULR1CPrimeFiberActual.cPFullFiber (T := T) b =
        thetaLamWeight  T b * cP_local b) :
    (∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight  T b *
          thetaContainerMass (T := T) (b := b) (cP_local b)) =
      -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2  T := by
  refine container_sum_eq_neg_Mpaper (T := T) cP_local
    (fun b => ?_) (fun b => ?_)
  · rw [← cPFullFiberLoc_eq (T := T) b]
    exact hcross b
  · exact MpaperB_eq_cPFullFiberLoc_mul_logp (T := T) b

/-- R1 container target with no hMb input: -M_paper_v2 <= container theta sum (equality). -/
theorem negM_le_thetaContainer_unconditional
    (cP_local : Bad (nativePlaceSelection T) → ℝ)
    (hcross : ∀ b : Bad (nativePlaceSelection T),
      Mzk1ULR1CPrimeFiberActual.cPFullFiber (T := T) b =
        thetaLamWeight  T b * cP_local b) :
    -LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2  T ≤
      ∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight  T b *
          thetaContainerMass (T := T) (b := b) (cP_local b) :=
  le_of_eq (container_sum_eq_neg_Mpaper_unconditional (T := T) cP_local hcross).symm

#print axioms container_sum_eq_neg_Mpaper_unconditional
#print axioms negM_le_thetaContainer_unconditional

end LeanFormal.IUT.XiFPaper.Mzk1URThetaContainerP5Actual
end