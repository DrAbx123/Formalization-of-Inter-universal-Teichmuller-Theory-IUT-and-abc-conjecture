/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5CountLocalValuationBridgeActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-!
# B5: generator norm/valuation bridges

Auxiliary inputs for LocalNormGeneratorBridge / CountValuationBridge:
* NormZpowBridge: norm = residueNormBase ^ localValuation (Mathlib norm_def target;
  base/exponent bookkeeping left explicit);
* CountValuationBridge: still reduces to CountLocalizationBridge (DVR span/count).
-/

noncomputable section
open scoped BigOperators NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5GeneratorNormBridgesActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open Multiplicative WithZero

variable {k : Type} [Field k] [NumberField k]
variable (v : NumberField.FinitePlace k)

def NormZpowBridge (x : LocalField (k := k) v) : Prop :=
  ‖x‖ = (residueNormBase v) ^ (localValuation (k := k) v x)

theorem localNormGeneratorBridge_of_normZpow
    {I : LineBundle (k := k)} (d : LocalGeneratorData (k := k) I v)
    (hb : NormZpowBridge (k := k) v d.generator) :
    LocalNormGeneratorBridge (k := k) d := by
  change Real.log ‖d.generator‖ =
    (localValuation (k := k) v d.generator : Real) * Real.log (residueNormBase v)
  have hgen : ‖d.generator‖ =
      (residueNormBase v) ^ (localValuation (k := k) v d.generator) := hb
  rw [hgen, Real.log_zpow]

def normBridgeRows : List (String × String × String) :=
  [ ("NormZpowBridge", "norm = residueNormBase ^ localValuation", "GAP (Mathlib norm_def base/exponent bookkeeping)"),
    ("localNormGeneratorBridge_of_normZpow", "log form of the norm bridge", "PROVED (conditional on NormZpowBridge)"),
    ("CountValuationBridge", "span/uniformizer vs count", "GAP (reduces to CountLocalizationBridge)") ]

theorem normBridgeRows_length : normBridgeRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1B5GeneratorNormBridgesActual

end