/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1DVRInstanceExportActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalGeneratorFromIsPrincipalActual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedFractionalIdealActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PlaceVolumeSignActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable {k : Type} [Field k] [NumberField k]

theorem dvr_isPrincipalIdealRing_instance
    (v : NumberField.FinitePlace k) :
    IsPrincipalIdealRing (NumberFieldFinitePlace.CompletionIntegers v) :=
  inferInstance

def dvrInstanceRows : List (String × String × String) :=
  [ ("dvr_isPrincipalIdealRing_instance", "DVR => PID", "GREEN") ]

end LeanFormal.IUT.XiFPaper.Mzk1P1DVRInstanceExportActual
