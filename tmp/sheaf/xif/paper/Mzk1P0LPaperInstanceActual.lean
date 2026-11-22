import tmp.sheaf.xif.paper.Mzk1S3137LReadoutActual
import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import tmp.sheaf.xif.paper.Mzk1C3LogShellTensorLActual
import Mathlib.Tactic

/-!
# P0: LPaper312Statement instance on actualSourcePilotRegionDataL

Instantiates the L-side q/theta readings on the actual L carrier.
The statement is recorded as a Prop; the exact first missing arrow is the
q-to-theta-hull containment/normalization, not constructed here.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137LReadoutActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open MeasureTheory

universe ua upi umon ui
variable {l : PrimeGeFive}

/-- The actual L carrier at a given place. -/
noncomputable def C3LAt
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) :
    SourcePilotRegionDataL (I := I) :=
  actualSourcePilotRegionDataL I place

/-- q-pilot reading instance on the actual L carrier. -/
noncomputable def qReadActual
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) : Real :=
  qPilotLogVolumeReadingL (C3LAt I place)

/-- Theta-hull log-volume instance on the actual L carrier. -/
noncomputable def thetaReadActual
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) : Real :=
  thetaPilotHullLogVolumeRealL (C3LAt I place)

theorem qReadActual_eq
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) :
    qReadActual I place = -|Real.log ‖(C3LAt I place).q.q‖| := by
  unfold qReadActual
  exact qPilotLogVolumeReadingL_eq_neg_abs (C3LAt I place)

theorem qReadActual_nonpos
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) :
    qReadActual I place ≤ 0 := by
  unfold qReadActual
  exact qPilotLogVolumeReadingL_nonpos (C3LAt I place)

theorem thetaReadActual_eq_rawHaar
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) :
    thetaReadActual I place =
      Real.log ((actualC3LogShellTensorHaarL (C3LAt I place))
        (actualC3LogShellTensorRegionL (C3LAt I place))).toReal := rfl

/-- P0 L-side comparison target on the actual L carrier. -/
def LPaperInstance
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) : Prop :=
  LPaper312Statement (C3LAt I place) (C3LAt I place)

/-- Conditional reduction: a nonnegative theta hull log-volume suffices. -/
theorem LPaperInstance_of_theta_nonneg
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
    (h : 0 ≤ thetaReadActual I place) : LPaperInstance I place := by
  unfold LPaperInstance LPaper312Statement
  exact le_trans (qReadActual_nonpos I place) h

/-- Exact first missing source arrow. -/
structure LQThetaSourceArrow
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) where
  q_mem_thetaRegion :
    (↑(C3LAt I place).tensorUnit : C3LogShellTensorBlockL (C3LAt I place)) ∈
      actualC3LogShellTensorRegionL (C3LAt I place)
  normalization_eq :
    thetaReadActual I place = Real.log ‖(C3LAt I place).q.q‖

def LQThetaSourceArrowMissing
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) : Prop :=
  Nonempty (LQThetaSourceArrow I place)

#print axioms qReadActual_eq
#print axioms qReadActual_nonpos
#print axioms thetaReadActual_eq_rawHaar
#check LQThetaSourceArrow

end LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
