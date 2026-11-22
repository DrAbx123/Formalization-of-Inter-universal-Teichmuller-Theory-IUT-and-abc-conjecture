/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import tmp.sheaf.gogopex.Iut.Stage1.PilotComparison
import tmp.sheaf.xif.paper.Mzk1XiFFormalStepActual

/-! # A518: containment bridge — Gogopex/xi-f membership to StepXI Cor312Conclusion -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexContainment

open LeanFormal.IUT
open Iut RealLineCopy
open LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual

/-- A Gogopex Stage-1 comparison gives the signed inequality `-q.value <= -theta.value`
(the bare Corollary 3.12 real inequality). -/
theorem signed_le_of_stage1Comparison (C : Stage1.Stage1Comparison) :
    -C.q.value ≤ -C.theta.value := 
  C.comparison

/-- Build the tree StepXI contract from a Gogopex Stage-1 comparison: `qSigned := -q.value`,
`thetaSigned := -theta.value`, with trivial target at `qSigned` and caller-supplied
IPL/SHE/APT evidence. -/
def stepXIContractOfComparison (C : Stage1.Stage1Comparison)
    (ipl she apt : Prop) (hi : ipl) (hs : she) (ha : apt) : StepXIContract where
  qSigned := -C.q.value
  thetaSigned := -C.theta.value
  targetSigned := -C.q.value
  q_negative := by
    have hpos : 0 < C.q.value := C.q_positive
    linarith
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hi
  she_evidence := hs
  apt_evidence := ha
  q_le_target := le_refl _
  target_le_theta := C.comparison

/-- The StepXI contract built from the Gogopex comparison satisfies `Cor312Conclusion`
(consumer of `cor312_of_constructed_stepXI`). -/
theorem cor312Conclusion_of_gogopexComparison (C : Stage1.Stage1Comparison)
    (ipl she apt : Prop) (hi : ipl) (hs : she) (ha : apt) :
    Cor312Conclusion (stepXIContractOfComparison C ipl she apt hi hs ha) :=
  cor312_of_constructed_stepXI _

/-- **xi-e containment bridge**: if the q-pilot log-volume lies in the set of possible
Theta-pilot log-volumes (calibrated xi-f data), then the StepXI contract built from those
signed values satisfies `Cor312Conclusion`. -/
theorem cor312Conclusion_of_membership (D : CalibratedPilots)
    (h : D.logq ∈ regionLe D.logTheta) :
    ∃ contract : StepXIContract, Cor312Conclusion contract := by
  have hqle : D.logq ≤ D.logTheta := xi_f_formal_step h
  have hqneg : D.logq < 0 := by
    have hq := D.hq
    have hpos := D.hAbsPos
    rw [hq]
    linarith
  let contract : StepXIContract := {
    qSigned := D.logq,
    thetaSigned := D.logTheta,
    targetSigned := D.logq,
    q_negative := hqneg,
    ipl := True,
    she := True,
    apt := True,
    ipl_evidence := trivial,
    she_evidence := trivial,
    apt_evidence := trivial,
    q_le_target := le_refl _,
    target_le_theta := hqle }
  exact ⟨contract, cor312_of_constructed_stepXI contract⟩

end LeanFormal.IUT.Objects.GogopexContainment
