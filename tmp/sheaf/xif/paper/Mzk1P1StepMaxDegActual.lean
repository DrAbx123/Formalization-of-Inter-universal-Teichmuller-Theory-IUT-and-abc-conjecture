import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeActual
import tmp.sheaf.xif.paper.Mzk1P1MeasureBridge3Actual
import tmp.sheaf.xif.paper.Mzk1F0StepGeometryActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1StepMaxDegActual — maxDegP non-increase for the concrete f0 step target

Real Lean (no sorry/axiom): the P1 maximal degree of the concrete step target stepSetP1
does not exceed maxDegP S, using: f0(S) values have degree <= their input degree
(degQ_aeval_le), conjugates of alpha0 have degree <= degQ alpha0 (minpoly divisibility),
critical values have strictly smaller degree (degQ_critValue_lt), and infinity has degree 1.
This is the first half (f4a) of the P1 measure transfer for the Problem C step provider.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1StepMaxDegActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge3Actual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual

attribute [local instance] Classical.decEq

universe u

/-- Values of f0 = minpoly on S have degree at most maxDegP S. -/
theorem maxDegP_image_step_le (S : Finset (P1Point Qbar)) (alpha0 : Qbar)
    (hmax : degQ alpha0 = maxDegP S) :
    maxDegP ((S ∪ (conjSet alpha0).image (fun x => P1Point.ofFinite x)).image (LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual.f0Map alpha0))
      <= maxDegP S := by
  unfold maxDegP
  apply Finset.sup_le
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  rcases Finset.mem_union.mp hq with hqS | hqC
  · cases q with
    | none =>
        -- f0(infinity) = infinity, degree 1 <= maxDegP S
        have h1 : degP (LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual.f0Map alpha0 (none : P1Point Qbar)) = 1 := by
          rw [show (none : P1Point Qbar) = P1Point.infty from rfl, LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual.f0Map_infty]
          rfl
        rw [h1]
        have hpos : 0 < degQ alpha0 := degQ_pos alpha0
        change 1 <= maxDegP S
        rw [← hmax]
        omega
    | some x =>
        have hdeg := degQ_aeval_le (minpoly ℚ alpha0) x
        have hxle : degQ x <= maxDegP S := by
          unfold maxDegP
          calc degQ x = degP (P1Point.ofFinite x) := rfl
            _ <= S.sup degP := Finset.le_sup (f := degP) hqS
        calc degP (LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual.f0Map alpha0 (P1Point.ofFinite x))
            = degQ (aeval x (minpoly ℚ alpha0)) := rfl
          _ <= degQ x := hdeg
          _ <= maxDegP S := hxle
  · obtain ⟨x, hxconj, rfl⟩ := Finset.mem_image.mp hqC
    have hroot : aeval x (minpoly ℚ alpha0) = 0 := mem_conjSet_iff.mp hxconj
    have hdvd : minpoly ℚ x ∣ minpoly ℚ alpha0 := minpoly.dvd ℚ x hroot
    have hne : minpoly ℚ alpha0 ≠ 0 := minpoly.ne_zero (isIntegral_Qbar alpha0)
    have hle : degQ x <= degQ alpha0 :=
      Polynomial.natDegree_le_of_dvd hdvd hne
    calc degP (LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual.f0Map alpha0 (P1Point.ofFinite x))
        = degQ (aeval x (minpoly ℚ alpha0)) := rfl
      _ <= degQ x := degQ_aeval_le (minpoly ℚ alpha0) x
      _ <= degQ alpha0 := hle
      _ = maxDegP S := hmax

/-- Critical-value images have degree strictly smaller than degQ alpha0. -/
theorem maxDegP_crit_image_le (S : Finset (P1Point Qbar)) (alpha0 : Qbar)
    (hmax : degQ alpha0 = maxDegP S) :
    maxDegP ((critSet alpha0).image
      (fun x => P1Point.ofFinite (aeval x (minpoly ℚ alpha0)))) <= maxDegP S := by
  unfold maxDegP
  apply Finset.sup_le
  intro p hp
  obtain ⟨x, hxc, rfl⟩ := Finset.mem_image.mp hp
  have hzero : aeval x (derivative (minpoly ℚ alpha0)) = 0 :=
    aeval_derivative_eq_zero_of_mem_critSet hxc
  have hlt : degQ (aeval x (minpoly ℚ alpha0)) < degQ alpha0 :=
    degQ_critValue_lt alpha0 x hzero
  calc degP (P1Point.ofFinite (aeval x (minpoly ℚ alpha0)))
      = degQ (aeval x (minpoly ℚ alpha0)) := rfl
    _ <= degQ alpha0 := le_of_lt hlt
    _ = S.sup degP := hmax

/-- f4a: the concrete step target does not increase the P1 maximal degree. -/
theorem maxDegP_stepSetP1_le (S : Finset (P1Point Qbar)) (alpha0 : Qbar)
    (hmax : degQ alpha0 = maxDegP S) :
    maxDegP (stepSetP1 S alpha0) <= maxDegP S := by
  have h1 := maxDegP_image_step_le S alpha0 hmax
  have h2 := maxDegP_crit_image_le S alpha0 hmax
  calc maxDegP (stepSetP1 S alpha0)
      = max (maxDegP ((S ∪ (conjSet alpha0).image (fun x => P1Point.ofFinite x)).image (LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual.f0Map alpha0)))
          (maxDegP ((critSet alpha0).image (fun x => P1Point.ofFinite (aeval x (minpoly ℚ alpha0))))) := by
        unfold stepSetP1
        rw [maxDegP_union]
        simp [LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual.f0Poly]
    _ <= maxDegP S := max_le h1 h2

/-- Row record. -/
def p1StepMaxDegRows : List (String × String) :=
  [ ("maxDegP_image_step_le", "PROVED"),
    ("maxDegP_crit_image_le", "PROVED"),
    ("maxDegP_stepSetP1_le (f4a)", "PROVED") ]

theorem p1StepMaxDegRows_length : p1StepMaxDegRows.length = 3 := rfl

#check maxDegP_stepSetP1_le

end LeanFormal.IUT.XiFPaper.Mzk1P1StepMaxDegActual
end
