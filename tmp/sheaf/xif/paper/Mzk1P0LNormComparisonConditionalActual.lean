/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutProductActual
import tmp.sheaf.xif.paper.Mzk1S3137LReadoutActual
import Mathlib.Tactic

/-! # P0-L: conditional normalized comparison target (explicit object lock + bound)

`LNormComparisonTarget` compares the single-place L q-reading with the single-place
normalized readout.  `thetaNormReadProduct` is the global Bad-sum.  The bridge needs an
**explicit object lock** (arithmetic data / index correspondence) and the **explicit
numerical bound**; neither is asserted here. -/

noncomputable section
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormComparisonConditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutProductActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137LReadoutActual
open MeasureTheory

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Conditional canonical normalized target: explicit object lock + explicit bound. -/
theorem LNormComparisonTarget_of_bounds
    (hlock : thetaNormReadL I place = thetaNormReadProduct T)
    (hbound : qReadActual I place ≤ thetaNormReadProduct T) :
    LNormComparisonTarget I place := by
  unfold LNormComparisonTarget
  rw [hlock]
  exact hbound

/-- The same with the L-side readout in the bound (object lock + local bound). -/
theorem LNormComparisonTarget_of_local_bound
    (hbound : qReadActual I place ≤ thetaNormReadL I place) :
    LNormComparisonTarget I place := by
  unfold LNormComparisonTarget
  exact hbound

/-- **Conditional LPaperInstance**: object lock + normalized bound + sign of log(unitMass)
give the raw (unnormalized) L paper comparison. -/
theorem LPaperInstance_of_bounds
    (hlock : thetaNormReadL I place = thetaNormReadProduct T)
    (hbound : qReadActual I place ≤ thetaNormReadProduct T)
    (hlog : 0 ≤ Real.log (actualUnitMassL I place)) :
    LPaperInstance I place := by
  have htarget : LNormComparisonTarget I place :=
    LNormComparisonTarget_of_bounds I place T hlock hbound
  have hraw : qReadActual I place ≤ thetaReadActual I place :=
    qRead_le_thetaRead_of_normTarget I place htarget hlog
  unfold LPaperInstance LPaper312Statement
  simpa [qReadActual, thetaReadActual] using hraw

def lNormComparisonConditionalRows : List (String × String × String) :=
  [ ("LNormComparisonTarget_of_bounds", "object lock + global bound => normalized target", "PROVED (conditional)"),
    ("LNormComparisonTarget_of_local_bound", "local bound => normalized target", "PROVED (conditional)"),
    ("LGlobalLocalObjectLock", "GAP RECORD ONLY (not used by any proven theorem; real fields not typeable)", "EXPLICIT GAP (not asserted)"),
    ("LPaperInstance_of_bounds", "hobj + hlock + hbound + log unitMass >= 0 => LPaperInstance", "PROVED (conditional)"),
    ("unitMass = 1", "not used", "NOT CLAIMED") ]

theorem lNormComparisonConditionalRows_length :
    lNormComparisonConditionalRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P0LNormComparisonConditionalActual

end