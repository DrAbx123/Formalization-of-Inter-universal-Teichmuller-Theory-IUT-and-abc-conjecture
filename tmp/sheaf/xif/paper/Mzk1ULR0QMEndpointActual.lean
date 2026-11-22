/- R0-c Q/M endpoint with the verified 1/(2l) convention:
     MpaperB_b = (1/(2l)) * cPFullFiber_b * log p,
     qPilotMass(cP) = -(cP/(2l)) * log p,
     w_b = thetaLamWeight_b/(2l),
   and the endpoint sum_b w_b * nu(J_b) = - Mpaper_v2.
   Inputs: nu(J_b) = -cP_b*logp_b; crosswalk cPFullFiber_b = thetaLamWeight_b*cP_b (R0-b, DONE);
   fiber log extraction Qb_b = cPFullFiber_b*logp_b (hprime); M_paper_v2 = (1/(2l)) sum_b Qb_b (R0.2 DONE).
   The 1/(2l) enters exactly once (in w / MpaperB); nu itself has no 1/(2l). -/
import tmp.sheaf.xif.paper.Mzk1ULR0FullFiberActual
import tmp.sheaf.xif.paper.Mzk1ULR0FiberCrosswalkActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR0QMEndpointActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0FullFiberActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0FiberCrosswalkActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0RealDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR1MpaperBWeightActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- R0-c: sum_b w_b * nu(J_b) = -Mpaper_v2 with w_b = thetaLamWeight_b/(2l),
    nu(J_b) = -cP_b*logp_b, under the R0-b crosswalk and fiber log extraction. -/
theorem sum_weight_nu_eq_neg_Mpaper
    (nuJ w logp : Bad (nativePlaceSelection T) → Real)
    (hν : ∀ b, nuJ b = - cP (l := l) T b * logp b)
    (hw : ∀ b, w b = thetaLamWeight T b / (2 * (l.value : Real)))
    (hcross : ∀ b, cPFullFiber (l := l) T b =
      thetaLamWeight T b * cP (l := l) T b)
    (hQb : ∀ b, Qb (T := T) b = cPFullFiber (l := l) T b * logp b) :
    (∑ b : Bad (nativePlaceSelection T), w b * nuJ b) =
      - M_paper_v2 (l := l) T := by
  have hl : (2 * (l.value : Real)) ≠ 0 := by
    have h : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
    positivity
  have hterm : ∀ b : Bad (nativePlaceSelection T),
      w b * nuJ b = -(1 / (2 * (l.value : Real))) * Qb (T := T) b := by
    intro b
    rw [hν b, hw b, hQb b, hcross b]
    field_simp [hl]
  calc (∑ b : Bad (nativePlaceSelection T), w b * nuJ b)
      = ∑ b : Bad (nativePlaceSelection T),
          (-(1 / (2 * (l.value : Real))) * Qb (T := T) b) :=
        Finset.sum_congr rfl (fun b _ => hterm b)
    _ = -(1 / (2 * (l.value : Real))) *
          ∑ b : Bad (nativePlaceSelection T), Qb (T := T) b := by
        rw [← Finset.mul_sum]
    _ = - M_paper_v2 (l := l) T := by
        rw [Mpaper_eq_half_sum_Qb (l := l) T]
        ring

#print axioms sum_weight_nu_eq_neg_Mpaper




end LeanFormal.IUT.XiFPaper.Mzk1ULR0QMEndpointActual