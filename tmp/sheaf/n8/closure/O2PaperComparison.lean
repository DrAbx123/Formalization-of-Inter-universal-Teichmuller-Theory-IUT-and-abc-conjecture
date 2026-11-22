import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer
import Mathlib

/-!
# O2 paper comparison from SourceInitialThetaData

Qualified paper input is SourceInitialThetaData: actual arithmetic, actual
places V -> NumberFieldPlace K, curve/clauses, and ClauseB qParameters at
finite places of F over the bad moduli places.

The paper-faithful O2 data chooses an actual finite F-place over a bad moduli
place and reads:

* q-side: the actual ClauseB FinitePlaceQCandidate q at that place;
  ThetaQ = -log ||q||.
* anab-side: the actual F-place local log-shell and its production
  LogShellVolumeConsumer index; ThetaAnab = log(index).

The comparison is ThetaQ = ThetaAnab.  SourceInitialThetaData supplies the
q-parameters for every F-place over a bad moduli place, but does not select a
single actual bad F-place; the exact missing source object is thus a bad
F-place choice (PaperBadFPlace).  No shell SourceDefinition31Data field and no
arbitrary place/region is used.  The comparison itself is not defined as its
own target: both sides are independently defined readouts.
-/

noncomputable section

namespace ABCBridge.N8.O2PaperComparison

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume

universe u

variable {l : PrimeGeFive}

/-- Actual bad finite F-place over a bad moduli place of the paper input. -/
structure PaperBadFPlace (D : SourceInitialThetaData l) where
  place : NumberField.FinitePlace D.candidate.arithmetic.F
  mem_bad : NumberFieldFinitePlace.comap place ∈ D.candidate.VbadMod

/-- Rational prime below the chosen bad F-place. -/
noncomputable abbrev PaperBadFPlace.prime {D : SourceInitialThetaData l}
    (W : PaperBadFPlace D) : Nat :=
  (NumberFieldFinitePlace.completionRationalPrime W.place).val

/-- The actual q candidate from ClauseB at the chosen bad F-place. -/
noncomputable def PaperBadFPlace.q {D : SourceInitialThetaData l}
    (W : PaperBadFPlace D) :
    NumberFieldFinitePlace.FinitePlaceQCandidate W.place :=
  D.clauseB.qParameter W.place W.mem_bad

/-- Paper q-side readout: negative log-norm of the actual ClauseB q. -/
noncomputable def PaperThetaQ {D : SourceInitialThetaData l}
    (W : PaperBadFPlace D) : ℝ :=
  -Real.log ‖((W.q).q)‖

/-- The actual local log-shell datum at the chosen bad F-place. -/
noncomputable def PaperBadFPlace.shell {D : SourceInitialThetaData l}
    (W : PaperBadFPlace D) : SourceLogShellDatum := by
  letI : Fact (Nat.Prime W.prime) :=
    ⟨(NumberFieldFinitePlace.completionRationalPrime W.place).2⟩
  exact sourceLocalLogShellDatum (K := D.candidate.arithmetic.F)
    (p := W.prime) ⟨W.place, rfl⟩

/-- Paper anab-side readout: log of the actual production log-shell volume
index at the chosen bad F-place. -/
noncomputable def PaperThetaAnab {D : SourceInitialThetaData l}
    (W : PaperBadFPlace D) : ℝ := by
  letI : Fact (Nat.Prime W.prime) :=
    ⟨(NumberFieldFinitePlace.completionRationalPrime W.place).2⟩
  exact Real.log (((logShellVolumeConsumer (K := CommonPrimeCompletion
    (K := D.candidate.arithmetic.F) ⟨W.place, rfl⟩)
    (p := W.prime)).index : ℝ))

/-- O2 paper comparison: the independently defined q-side and anab-side
readouts agree. -/
def O2PaperComparison {D : SourceInitialThetaData l}
    (W : PaperBadFPlace D) : Prop :=
  PaperThetaQ W = PaperThetaAnab W

/-- Actual q-side positivity: q is nonzero and has norm < 1, so its negative
log-norm is positive. -/
theorem PaperThetaQ_pos {D : SourceInitialThetaData l}
    (W : PaperBadFPlace D) : 0 < PaperThetaQ W := by
  unfold PaperThetaQ
  have hq : (W.q).q ≠ 0 := (W.q).q_ne_zero
  have hpos : 0 < ‖((W.q).q)‖ := norm_pos_iff.mpr hq
  have hlt : ‖((W.q).q)‖ < 1 := by
    exact ArithmeticQPilotLogVolume.qNorm_lt_one (W.q)
  have hlog : Real.log ‖((W.q).q)‖ < 0 := Real.log_neg hpos hlt
  linarith

/-- Exact source gap: no actual bad finite F-place is selected by the paper
input.  ClauseB supplies qParameters only relative to an already chosen F-place
over the bad moduli place. -/
def PaperBadFPlaceGap (D : SourceInitialThetaData l) : Prop :=
  Nonempty (PaperBadFPlace D)

/-- Exact O2 comparison gap: existence of a chosen bad F-place at which the two
independently defined paper readouts agree.  This does not define either side
from the comparison. -/
def O2PaperComparisonGap (D : SourceInitialThetaData l) : Prop :=
  ∃ W : PaperBadFPlace D, O2PaperComparison W

end ABCBridge.N8.O2PaperComparison
