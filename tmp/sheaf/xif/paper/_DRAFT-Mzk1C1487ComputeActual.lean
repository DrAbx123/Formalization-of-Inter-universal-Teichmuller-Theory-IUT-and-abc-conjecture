/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import Mathlib.Tactic

/-! # A985: S1487 concrete data for l = 7 (and 11/13) -/

/-
Green ingredients confirmed from S1487:
* `S1487OriginalInput (S : SourceDefinition31Data l) :
   OriginalInput.{0,0,0,0,0} l S1487W` (:379-386) -- a CONCRETE OriginalInput builder;
* `S1487FaithfulInput : OriginalInput.{0,0,0,0,0} l S1487W` (:537-539);
* `S1487FaithfulC3 : SourcePilotRegionDataL (I := S1487FaithfulInput)` (:548-550),
  built with `actualSourcePilotRegionDataL ... S1487FivePlace`;
* `S1487FaithfulC3_q : (S1487FaithfulC3).q = S1487Cand` (:563-564);
* `S1487W := FinitePrimePlace 2 7` (:177);
* `S1487Cand` (:133) is `Classical.choice (finitePlaceQCandidate_nonempty ...)`, so the
  q VALUE (and its order) is NOT numerically determined by definition; only the residue
  norm is known: `S1487_residueNormBase_five : residueNormBase S1487FivePlace.val = 5`.

This file instantiates the concrete data at `l = 7` and records the computability boundary.
No sorry/axiom. -/

-/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1C1487ComputeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual

def primeGeFive7 : PrimeGeFive where
  value := 7
  prime := by norm_num
  ge_five := by norm_num

def primeGeFive11 : PrimeGeFive where
  value := 11
  prime := by norm_num
  ge_five := by norm_num

def primeGeFive13 : PrimeGeFive where
  value := 13
  prime := by norm_num
  ge_five := by norm_num

theorem primeGeFive7_value : primeGeFive7.value = 7 := rfl

/-- Concrete `OriginalInput` for `l = 7` (S1487 faithful data). -/
noncomputable def faithfulInput7 :
    OriginalInput.{0, 0, 0, 0, 0} primeGeFive7 S1487W :=
  S1487FaithfulInput

/-- Concrete S1391 L-carrier C3 for `l = 7`. -/
noncomputable def faithfulC37 :
    SourcePilotRegionDataL (l := primeGeFive7) (I := faithfulInput7) :=
  S1487FaithfulC3

/-- The C3 q is the chosen Gaussian candidate (noncomputable choice). -/
theorem faithfulC37_q : (faithfulC37).q = S1487Cand := rfl

def s1487Rows : List (String × String) :=
  [ ("S1487OriginalInput", "concrete OriginalInput builder (:379)", "GREEN") ,
    ("S1487FaithfulInput", "OriginalInput at S1487W (:537)", "GREEN") ,
    ("S1487FaithfulC3", "SourcePilotRegionDataL via actualSourcePilotRegionDataL (:548)", "GREEN") ,
    ("faithfulInput7 / faithfulC37", "instantiated at l=7", "GREEN") ,
    ("q value/order", "S1487Cand = Classical.choice ... (:133); no numeric order", "NOT NUMERIC") ,
    ("residue norm at place", "S1487_residueNormBase_five = 5", "GREEN") ,
    ("A/T/H/V", "A = -log ||S1487Cand.q|| symbolic; T/H/V need L tensor/Haar instantiation", "PARTIAL") ,
    ("R", "Hecke-side data", "MISSING") ]

theorem s1487Rows_length : s1487Rows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1C1487ComputeActual
