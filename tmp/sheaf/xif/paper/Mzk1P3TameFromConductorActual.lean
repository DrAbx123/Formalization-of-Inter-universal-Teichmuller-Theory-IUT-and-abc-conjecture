/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.Mzk1P3UnramResidueActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import Mathlib.Tactic

/-! # P3 tame-from-conductor: conditional hypotheses and the named derivation target

GAP-labeled file: the tame conductor hypotheses (l >= 11 and l does not divide e)
and the target implication to UnramResidueData at every bad place are recorded;
the local-field derivation itself is NOT asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3TameFromConductorActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1P3UnramResidueActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

def TameConductorHypotheses (C : PrimeConductorCurve) : Prop :=
  11 ≤ l.value ∧ ¬ (l.value ∣ C.e) ∧ C.e ≠ 0

def TameDerivationTarget (C : PrimeConductorCurve) : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    UnramResidueData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)

def tameConclusion (C : PrimeConductorCurve) (b : Bad (nativePlaceSelection T)) : Prop :=
  relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1
    ∧ relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1

theorem tameConclusion_iff_unramResidueData
    (C : PrimeConductorCurve) (b : Bad (nativePlaceSelection T)) :
    tameConclusion T C b ↔
      UnramResidueData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) :=
  Iff.rfl

def tameRows : List (String × String × String) :=
  [ ("TameConductorHypotheses", "l >= 11, l does not divide e, e nonzero", "DEF (input)"),
    ("tameConclusion", "relative e = f = 1 at a bad place", "DEF (conclusion)"),
    ("tameConclusion_iff_unramResidueData", "conclusion shape matches UnramResidueData", "PROVED (rfl)"),
    ("TameDerivationTarget", "tame hypotheses => e=f=1 at every bad place", "GAP-PC-TAME (content input)") ]

theorem tameRows_length : tameRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3TameFromConductorActual

end
