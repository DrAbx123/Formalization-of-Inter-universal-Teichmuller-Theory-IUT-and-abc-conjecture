import tmp.sheaf.xif.paper.Mzk1P1StepProviderDecompositionActual
import tmp.sheaf.xif.paper.Mzk1P1MeasureBridgeActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1StepMaxDeg2Actual — f4a (P1 max-degree non-increase) via finite decomposition

Real Lean (no sorry/axiom): on the selected finite maximal point, the P1 step target keeps
maxDegP bounded by maxDegP S.  Proof via the finite-part decomposition and the PROVED finite
f4a maxDeg_stepSet_le.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1StepMaxDeg2Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderDecompositionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridgeActual

local instance instDecEqQbar : DecidableEq Qbar := Classical.decEq Qbar
local instance instDecEqP1 : DecidableEq (P1Point Qbar) := Classical.decEq (P1Point Qbar)

universe u

theorem maxDeg_finitePart_eq_maxDegP (S : Finset (P1Point Qbar)) (alpha0 : Qbar)
    (halpha0S : P1Point.ofFinite alpha0 ∈ S) (hdeg : degQ alpha0 = maxDegP S) :
    maxDeg (finitePart S) = maxDegP S := by
  have halphaF : alpha0 ∈ finitePart S := mem_finitePart_iff.mpr halpha0S
  have hle1 : maxDeg (finitePart S) <= maxDegP S := by
    unfold maxDeg maxDegP
    exact Finset.sup_le_iff.mpr (fun x hx => by
      have hle := Finset.le_sup (f := degP) (mem_finitePart_iff.mp hx)
      have hdeg : degP (P1Point.ofFinite x) = degQ x := rfl
      rwa [hdeg] at hle)
  have hle2 : maxDegP S <= maxDeg (finitePart S) := by
    unfold maxDegP maxDeg
    exact Finset.sup_le_iff.mpr (fun p hp => by
      cases p with
      | none =>
          change (1 : ℕ) <= (finitePart S).sup degQ
          have hpos : 1 <= degQ alpha0 := by
            have := degQ_pos alpha0
            omega
          exact le_trans hpos (Finset.le_sup (f := degQ) halphaF)
      | some y =>
          have hle := Finset.le_sup (f := degQ) (mem_finitePart_iff.mpr hp)
          have hdeg : degP (some y) = degQ y := rfl
          rwa [← hdeg] at hle)
  exact le_antisymm hle1 hle2

theorem maxDegP_stepSetP1_le_alt (S : Finset (P1Point Qbar)) (alpha0 : Qbar)
    (halpha0S : P1Point.ofFinite alpha0 ∈ S) (hdeg : degQ alpha0 = maxDegP S) :
    maxDegP (stepSetP1 S alpha0) <= maxDegP S := by
  have hF : maxDeg (finitePart S) = maxDegP S :=
    maxDeg_finitePart_eq_maxDegP S alpha0 halpha0S hdeg
  have hmaxF : degQ alpha0 = maxDeg (finitePart S) := by rw [hdeg, hF]
  have hfin : maxDeg (stepSet (finitePart S) alpha0) <= maxDeg (finitePart S) :=
    maxDeg_stepSet_le (finitePart S) alpha0 (mem_finitePart_iff.mpr halpha0S) hmaxF
  have hdec := stepSetP1_eq_finite S alpha0
  have h1le : 1 <= maxDegP S := by
    have hpos : 1 <= degQ alpha0 := degQ_pos alpha0
    rw [hdeg] at hpos
    exact hpos
  by_cases hinf : P1Point.infty ∈ S
  · have hset : stepSetP1 S alpha0 =
        insert P1Point.infty
          ((stepSet (finitePart S) alpha0).image (fun x => P1Point.ofFinite x)) := by
      rw [hdec, if_pos hinf, Finset.insert_eq, Finset.union_comm]
    rw [hset, maxDegP_insert_infty_image]
    exact max_le h1le (le_trans hfin (le_of_eq hF))
  · have hset : stepSetP1 S alpha0 =
        (stepSet (finitePart S) alpha0).image (fun x => P1Point.ofFinite x) := by
      rw [hdec, if_neg hinf]
      exact Finset.union_empty _
    rw [hset, maxDegP_image_ofFinite]
    exact le_trans hfin (le_of_eq hF)

#check maxDegP_stepSetP1_le_alt

end LeanFormal.IUT.XiFPaper.Mzk1P1StepMaxDeg2Actual
end
