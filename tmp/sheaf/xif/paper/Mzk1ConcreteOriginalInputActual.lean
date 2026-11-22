/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import Mathlib.Tactic

/-! # A984: concrete prime labels and boundary data for l = 7 (and 11, 13) -/

Green ingredients from A982:
* `PrimeGeFive` (`LeanFormal/IUT/Foundations/Arithmetic/PrimeLabels.lean:14`) =
  `{value, prime, ge_five}`;
* `concreteInput l` (`SourceProcessionBoundary.lean:431`, olean TRUE): complete boundary
  `Input (V := FinitePrimePlace 2 7)`;
* `S1487FaithfulSourceData : SourceDefinition31Data.{0} l`
  (`S1487OQPilotScalarEqualityActual.lean:520`, olean TRUE).

GAP: no concrete `OriginalInput` assembly (boundary + source data -> OriginalInput) and no
found `SourceDefinition31Data -> OriginalInput` builder; also no N8NativeInput instance.
The file therefore constructs the concrete prime labels, the boundary and the source data,
and records the assembly gap explicitly (no fake OriginalInput). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ConcreteOriginalInputActual

open LeanFormal.IUT

/-- `l = 7` as a `PrimeGeFive`. -/
def primeGeFive7 : PrimeGeFive where
  value := 7
  prime := by norm_num
  ge_five := by norm_num

/-- `l = 11`. -/
def primeGeFive11 : PrimeGeFive where
  value := 11
  prime := by norm_num
  ge_five := by norm_num

/-- `l = 13`. -/
def primeGeFive13 : PrimeGeFive where
  value := 13
  prime := by norm_num
  ge_five := by norm_num

theorem primeGeFive7_value : primeGeFive7.value = 7 := rfl
theorem primeGeFive11_value : primeGeFive11.value = 11 := rfl
theorem primeGeFive13_value : primeGeFive13.value = 13 := rfl

/-- Concrete source boundary for `l = 7` (green `concreteInput`). -/
noncomputable def boundary7 :=
  concreteInput primeGeFive7

/-- Concrete faithful `SourceDefinition31Data` for `l = 7` (green S1487). -/
noncomputable def sourceData7 : SourceDefinition31Data.{0} primeGeFive7 :=
  S1487FaithfulSourceData (l := primeGeFive7)

/-- The concrete shared `Fmod` base field is available from the source data. -/
def sourceData7_baseField : Type := sourceData7.arithmetic.F

def concreteRows : List (String × String) :=
  [ ("primeGeFive7/11/13", "PrimeGeFive instances (value/prime/ge_five)", "PROVED") ,
    ("boundary7", "concreteInput primeGeFive7 (SourceProcessionBoundary:431)", "GREEN TERM") ,
    ("sourceData7", "S1487FaithfulSourceData (S1487:520)", "GREEN TERM") ,
    ("OriginalInput assembly", "boundary + source data -> OriginalInput", "GAP (no builder found)") ,
    ("N8NativeInput instance", "concrete native input", "GAP (no instance found)") ]

theorem concreteRows_length : concreteRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ConcreteOriginalInputActual
