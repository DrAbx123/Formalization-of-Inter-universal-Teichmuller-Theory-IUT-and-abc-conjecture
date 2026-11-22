/- R1.1 assembly (kurt), abstract hull-mass form (avoids blocked root-hull imports):
from the DONE endpoint sum_weight_nu_eq_neg_Mpaper (weights thetaLamWeight/(2l)) and the per-b mass
comparison nu(J_b) <= nuHull_b, derive -M_paper_v2 <= Sum_b (thetaLamWeight_b/(2l)) * nuHull_b.
Instantiation nuHull := arithmeticTupleNormalizedLogVolume (rootNormHull) is a separate DONE-or-queued
step (RootNormalizedContainmentActual / RootHullContainmentInequalityActual are NO-EVENT).
-/
import tmp.sheaf.xif.paper.Mzk1ULR0QMEndpointActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1ULR1CPrimeFiberActual
import tmp.sheaf.xif.paper.Mzk1ULQbVecActual
import tmp.sheaf.xif.paper.Mzk1ULThetaLamWeightPosActual
import tmp.sheaf.xif.paper.Mzk1ULR0RealDictionaryActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URPaperThetaR1FinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0QMEndpointActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULR1CPrimeFiberActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual
open LeanFormal.IUT.XiFPaper.Mzk1ULThetaLamWeightPosActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0RealDictionaryActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- R1.1: -M_paper_v2 <= the theta-weighted hull mass sum, from the endpoint sum and the
per-b comparison nu(J_b) <= nuHull_b. -/
theorem neg_Mpaper_le_paperThetaSum
    (nuJ nuHull logp : Bad (nativePlaceSelection T) → ℝ)
    (hnu : ∀ b, nuJ b = - cP T b * logp b)
    (hcross : ∀ b, cPFullFiber T b =
      thetaLamWeight T b * cP T b)
    (hQb : ∀ b, Qb (T := T) b =
      cPFullFiber T b * logp b)
    (hle : ∀ b, nuJ b ≤ nuHull b) :
    -M_paper_v2 T ≤
      ∑ b : Bad (nativePlaceSelection T),
        (thetaLamWeight T b / (2 * (l.value : ℝ))) * nuHull b := by
  have hsum := sum_weight_nu_eq_neg_Mpaper T
    nuJ (fun b => thetaLamWeight T b / (2 * (l.value : ℝ))) logp
    hnu (fun b => rfl) hcross hQb
  have hl0 : ∀ b, 0 ≤ thetaLamWeight T b / (2 * (l.value : ℝ)) := by
    intro b
    have h1 : 0 ≤ thetaLamWeight T b := le_of_lt (thetaLamWeight_pos T b)
    have h2 : (0 : ℝ) < 2 * (l.value : ℝ) := by
      have := l.prime.pos
      positivity
    exact div_nonneg h1 (le_of_lt h2)
  have := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Bad (nativePlaceSelection T)))) =>
    mul_le_mul_of_nonneg_left (hle b) (hl0 b))
  rw [hsum] at this
  exact this

#print axioms neg_Mpaper_le_paperThetaSum

end LeanFormal.IUT.XiFPaper.Mzk1URPaperThetaR1FinalActual
end