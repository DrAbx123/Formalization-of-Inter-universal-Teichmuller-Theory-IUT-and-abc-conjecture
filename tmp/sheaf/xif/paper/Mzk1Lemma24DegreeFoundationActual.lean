import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.Mzk1Lemma24ValueDegreeDropActual
import tmp.sheaf.xif.paper.Mzk1Lemma24StepProviderActual
import Mathlib.Tactic

/-! # Mzk1Lemma24DegreeFoundationActual — reusable REAL degree foundation layer (Lemma 2.4)

STEP 0 prior-art (reuse, no re-proof): Mzk1NestedInductionActual (Qbar, degQ, maxDeg,
numMax, isIntegral_Qbar, degQ_pos, degQ_critValue_lt), Mzk1Lemma24ValueDegreeDropActual
(ValueDegreeDropStatement / valueDegreeDrop_proved; FieldDegreeDropStatement /
fieldDegreeDrop_proved), Mzk1Lemma24StepProviderActual (statement definitions).

SCOPE / INTEGRITY (recompile 2026-11-10T23:50): real definitions + unconditional PROVED theorems only (no named
inputs); reusable by Problem C consumers.  No closure claim. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24DegreeFoundationActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24ValueDegreeDropActual
open scoped Classical

/-- Reduced degree over Q: deg_Q(alpha) - 1 (paper m/d bookkeeping). -/
def reducedDegreeOfPoint (alpha : Qbar) : Nat := degQ alpha - 1

/-- Field of definition of an algebraic number: Q(alpha) inside Qbar. -/
def fieldOfDefinition (alpha : Qbar) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ ({alpha} : Set Qbar)

/-- The field of definition has Q-degree equal to deg_Q(alpha). -/
theorem fieldOfDefinition_finrank (alpha : Qbar) :
    Module.finrank ℚ (fieldOfDefinition alpha) = degQ alpha :=
  IntermediateField.adjoin.finrank (isIntegral_Qbar alpha)

/-- Undirected maximal reduced degree of a finite point set (0 for the empty set). -/
def maxReducedDegree (S : Finset Qbar) : Nat := S.sup reducedDegreeOfPoint

/-- The undirected measure pair (maxDeg, numMax). -/
def degreeMeasure (S : Finset Qbar) : Nat × Nat := (maxDeg S, numMax S)

/-- Reduced degree strictly decreases when deg_Q strictly decreases. -/
theorem reducedDegree_lt_of_degQ_lt {alpha beta : Qbar} (h : degQ beta < degQ alpha) :
    reducedDegreeOfPoint beta < reducedDegreeOfPoint alpha := by
  unfold reducedDegreeOfPoint
  have hb : 0 < degQ beta := degQ_pos beta
  omega

/-- Maximal reduced degree is monotone under subsets. -/
theorem maxReducedDegree_mono {S T : Finset Qbar} (h : S ⊆ T) :
    maxReducedDegree S ≤ maxReducedDegree T := by
  unfold maxReducedDegree
  exact Finset.sup_mono h

/-- Critical values of a Q-polynomial: a uniform degree bound statement (undirected). -/
def criticalValueDegreeBound (q : Polynomial ℚ) : Prop :=
  forall xi : Qbar, aeval xi (derivative q) = 0 → degQ (aeval xi q) ≤ q.natDegree - 1

/-- f0 = minpoly satisfies the undirected critical-value degree bound (paper Lemma 2.4
lines 195-199; reuse of the PROVED degQ_critValue_lt). -/
theorem minpoly_criticalValueDegreeBound (alpha0 : Qbar) :
    criticalValueDegreeBound (minpoly ℚ alpha0) := by
  intro xi hxi
  have h := degQ_critValue_lt alpha0 xi hxi
  have hd : degQ alpha0 = (minpoly ℚ alpha0).natDegree := rfl
  show degQ (aeval xi (minpoly ℚ alpha0)) ≤ (minpoly ℚ alpha0).natDegree - 1
  omega

/-- Reduced-degree form: every critical value has strictly smaller reduced degree. -/
theorem criticalValue_reducedDegree_lt (alpha0 xi : Qbar)
    (hxi : aeval xi (derivative (minpoly ℚ alpha0)) = 0) :
    reducedDegreeOfPoint (aeval xi (minpoly ℚ alpha0)) < reducedDegreeOfPoint alpha0 :=
  reducedDegree_lt_of_degQ_lt (degQ_critValue_lt alpha0 xi hxi)

/-- Undirected critical-value reduced degree bound: at most natDegree(f0) - 2. -/
theorem criticalValue_reducedDegree_le (alpha0 xi : Qbar)
    (hxi : aeval xi (derivative (minpoly ℚ alpha0)) = 0) :
    reducedDegreeOfPoint (aeval xi (minpoly ℚ alpha0)) ≤ (minpoly ℚ alpha0).natDegree - 2 := by
  have h := degQ_critValue_lt alpha0 xi hxi
  have hd : degQ alpha0 = (minpoly ℚ alpha0).natDegree := rfl
  unfold reducedDegreeOfPoint
  have hpos : 0 < degQ (aeval xi (minpoly ℚ alpha0)) := degQ_pos _
  omega

/-- Re-exported PROVED (S1b) value-degree drop statement. -/
theorem valueDegreeDrop_reexport :
    LeanFormal.IUT.XiFPaper.Mzk1Lemma24StepProviderActual.ValueDegreeDropStatement :=
  valueDegreeDrop_proved

/-- Re-exported PROVED (S1 full) field-degree drop statement. -/
theorem fieldDegreeDrop_reexport :
    LeanFormal.IUT.XiFPaper.Mzk1Lemma24StepProviderActual.FieldDegreeDropStatement :=
  fieldDegreeDrop_proved

/-- Value-degree bound in reduced form: deg_Q(f0(x)) <= deg_Q(x).  (aeval values lie in
Q(x); tower degrees; proved via degQ_aeval_le in the nested-induction file.) -/
theorem aeval_reducedDegree_le (alpha : Qbar) (f : Polynomial ℚ) :
    reducedDegreeOfPoint (aeval alpha f) ≤ reducedDegreeOfPoint alpha := by
  unfold reducedDegreeOfPoint
  have h : degQ (aeval alpha f) ≤ degQ alpha := degQ_aeval_le f alpha
  omega

/-- Rows: real definitions + unconditional proved theorems. -/
def degreeFoundationRows : List (String × String × String) :=
  [ ("reducedDegreeOfPoint", "DEFINED", "degQ alpha - 1")
  , ("fieldOfDefinition + finrank", "DEFINED + PROVED", "fieldOfDefinition_finrank = degQ alpha")
  , ("maxReducedDegree / degreeMeasure", "DEFINED", "undirected finite-set measure")
  , ("criticalValueDegreeBound + minpoly case", "DEFINED + PROVED", "minpoly_criticalValueDegreeBound (degQ_critValue_lt)")
  , ("critical-value reduced degree", "PROVED", "criticalValue_reducedDegree_lt / _le (undirected)")
  , ("value-degree drop / field-degree drop", "PROVED (re-export)", "valueDegreeDrop_proved / fieldDegreeDrop_proved")
  , ("aeval degree bound", "PROVED", "aeval_reducedDegree_le (degQ_aeval_le)")
  , ("scope", "REAL LAYER, NO NAMED INPUT", "unconditional defs+proofs; no closure claim") ]

theorem degreeFoundationRows_length : degreeFoundationRows.length = 8 := rfl

#check reducedDegreeOfPoint
#check fieldOfDefinition_finrank
#check minpoly_criticalValueDegreeBound
#check criticalValue_reducedDegree_lt

end LeanFormal.IUT.XiFPaper.Mzk1Lemma24DegreeFoundationActual
end
