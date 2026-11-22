import tmp.sheaf.xif.paper.Mzk1E1OrderActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

/-! # A942: explicit q candidate and the bare E1 failure

A concrete q candidate is chosen from the DVR existence theorem; its exponent is positive.
For its local signed log, the q-side contribution is nonzero, so the bare
E1PaperScaledHullForm fails by Mzk1E1OrderActual.e1_iff_qside_zero. This is a
parameterized explicit-data counterexample, not a full SourceDefinition31Data term. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1E1ExplicitCounterexampleActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1E1OrderActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume

/-- Explicit q candidate at an arbitrary actual finite place (choice of the DVR
uniformizer existence theorem). -/
noncomputable def explicitQCandidate
    {K : Type*} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) : FinitePlaceQCandidate place :=
  Classical.choice (finitePlaceQCandidate_nonempty place)

/-- The explicit candidate has positive q-order. -/
theorem explicitQCandidate_exponent_pos
    {K : Type*} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) :
    0 < (explicitQCandidate place).exponent :=
  FinitePlaceQCandidate.exponent_pos _

/-- Its local signed log is nonzero, hence the q-side contribution is nonzero. -/
theorem explicitQCandidate_qSide_ne_zero
    {K : Type*} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) :
    QSideContribution (localSignedLog (explicitQCandidate place)) ≠ 0 := by
  unfold QSideContribution
  exact neg_ne_zero.mpr (ne_of_lt (localSignedLog_neg _))

/-- Bare E1 form fails for the explicit local q candidate. -/
theorem bareE1_false_for_explicit_local_q
    {K : Type*} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) :
    ¬ E1PaperScaledHullForm
      (QSideContribution (localSignedLog (explicitQCandidate place))) := by
  rw [e1_iff_qside_zero]
  exact explicitQCandidate_qSide_ne_zero place

end LeanFormal.IUT.XiFPaper.Mzk1E1ExplicitCounterexampleActual
