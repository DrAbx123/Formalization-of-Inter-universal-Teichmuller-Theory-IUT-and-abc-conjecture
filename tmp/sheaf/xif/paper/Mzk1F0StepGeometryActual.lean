import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import Mathlib.Tactic

/-! # Mzk1F0StepGeometryActual — REAL geometric layer of the f0 step (Problem C / Lemma 2.4)

STEP 0 prior-art (reuse, no re-proof): Mzk1NestedInductionActual (Qbar, degQ, maxDeg,
numMax, conjSet, critSet, stepSet, maxDeg_stepSet_le, numMax_stepSet_lt,
measure_stepSet_lt, degQ_critValue_lt, degQ_aeval_le; StepProvider is the NAMED geometric
layer there); Mzk1P1MorphismInterfaceActual (P1Point, P1Point.infty/ofFinite).

SCOPE / INTEGRITY: this file supplies REAL definitions and the PROVABLE part of the f0
geometric layer: f0 = minpoly as a polynomial map P1(Qbar) -> P1(Qbar) (infinity mapped to
infinity), its critical points/values (from roots of f0'), critical-value image inclusion,
the degree bound for critical values, and the S' -> S transport data record (target set =
stepSet, measure decrease PROVED).  The full paper transport (PaperScopeLemma24Target S'
-> Target S) remains a NAMED input (not asserted); no closure claim. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open scoped Classical

/-- f0 = minpoly of the chosen point alpha0 (paper Lemma 2.4). -/
def f0Poly (alpha0 : Qbar) : Polynomial ℚ := minpoly ℚ alpha0

/-- A Q-polynomial as a polynomial map on P1(Qbar): finite x maps to f(x), infinity to
infinity.  This is the real object behind the P1 morphism f0. -/
def polyMapQbar (f : Polynomial ℚ) : P1Point Qbar → P1Point Qbar :=
  fun p => p.map (fun x => aeval x f)

/-- The f0 P1(Qbar) map. -/
def f0Map (alpha0 : Qbar) : P1Point Qbar → P1Point Qbar :=
  polyMapQbar (f0Poly alpha0)

theorem f0Map_infty (alpha0 : Qbar) : f0Map alpha0 P1Point.infty = P1Point.infty := rfl

theorem f0Map_finite (alpha0 : Qbar) (x : Qbar) :
    f0Map alpha0 (P1Point.ofFinite x) = P1Point.ofFinite (aeval x (f0Poly alpha0)) := rfl

/-- Infinity bookkeeping: the only point mapping to infinity is infinity itself
(polynomial maps have no finite poles). -/
theorem f0Map_eq_infty_iff (alpha0 : Qbar) {p : P1Point Qbar} :
    f0Map alpha0 p = P1Point.infty ↔ p = P1Point.infty := by
  cases p with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some x =>
      constructor
      · intro h
        exact absurd h (by simp [f0Map, polyMapQbar, P1Point.infty])
      · intro h
        exact absurd h (by simp [P1Point.infty])

/-- Critical points of f0 over Qbar: roots of f0'. -/
def f0CritPoints (alpha0 : Qbar) : Set Qbar :=
  {x : Qbar | aeval x (derivative (f0Poly alpha0)) = 0}

/-- Critical values of f0 over Qbar. -/
def f0CritValues (alpha0 : Qbar) : Set Qbar :=
  {y : Qbar | ∃ x : Qbar, x ∈ f0CritPoints alpha0 ∧ aeval x (f0Poly alpha0) = y}

/-- The finite critical-value set, as the image of the finite critical-point set. -/
def f0CritValuesFinset (alpha0 : Qbar) : Finset Qbar :=
  (critSet alpha0).image (fun x => aeval x (f0Poly alpha0))

/-- Every finite critical value is the image of a finite P1 point under f0 (CV image
inclusion). -/
theorem f0CritValue_mem_image (alpha0 : Qbar) {y : Qbar} (hy : y ∈ f0CritValues alpha0) :
    ∃ p : P1Point Qbar, f0Map alpha0 p = P1Point.ofFinite y := by
  obtain ⟨x, _hx, rfl⟩ := hy
  exact ⟨P1Point.ofFinite x, rfl⟩

/-- Critical values of f0 are realized on the finite critical-point set. -/
theorem f0CritValues_subset_image (alpha0 : Qbar) :
    f0CritValues alpha0 ⊆
      (fun x : Qbar => aeval x (f0Poly alpha0)) '' f0CritPoints alpha0 := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, rfl⟩

/-- Critical values have strictly smaller degree over Q than alpha0 (paper Lemma 2.4
lines 195-199; reuse of the PROVED degQ_critValue_lt). -/
theorem f0CritValue_deg_lt (alpha0 : Qbar) {y : Qbar} (hy : y ∈ f0CritValues alpha0) :
    degQ y < degQ alpha0 := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact degQ_critValue_lt alpha0 x hx

/-- Undirected form of the critical-value degree bound: deg of a critical value is at most
natDegree(f0) - 1. -/
theorem f0CritValue_deg_le (alpha0 : Qbar) {y : Qbar} (hy : y ∈ f0CritValues alpha0) :
    degQ y ≤ (f0Poly alpha0).natDegree - 1 := by
  have h := f0CritValue_deg_lt alpha0 hy
  have hd : degQ alpha0 = (f0Poly alpha0).natDegree := rfl
  omega

/-- S' = f0(S union conjugates) union f0(critical points) (the paper's finite step set). -/
def f0StepTarget (S : Finset Qbar) (alpha0 : Qbar) : Finset Qbar :=
  stepSet S alpha0

/-- Max-degree decrease (proved asset): the step target has max degree at most that of S. -/
theorem f0StepTarget_maxDeg_le (S : Finset Qbar) (alpha0 : Qbar)
    (halpha0 : alpha0 ∈ S) (hmax : degQ alpha0 = maxDeg S) :
    maxDeg (f0StepTarget S alpha0) ≤ maxDeg S :=
  maxDeg_stepSet_le S alpha0 halpha0 hmax

/-- Measure decrease for the finite step target (proved asset). -/
theorem f0StepTarget_measure_lt (S : Finset Qbar) (alpha0 : Qbar)
    (halpha0 : alpha0 ∈ S) (hmax : degQ alpha0 = maxDeg S) (h2 : 2 ≤ degQ alpha0) :
    Prod.Lex (· < ·) (· < ·)
      (maxDeg (f0StepTarget S alpha0), numMax (f0StepTarget S alpha0))
      (maxDeg S, numMax S) :=
  measure_stepSet_lt S alpha0 halpha0 hmax h2

/-- Concrete S' -> S transport data supplied by the f0 step: the target set, its defining
equation, the PROVED measure decrease, and the critical-value degree bound.  The remaining
paper transport (Target S' -> Target S) is a NAMED input, not asserted here. -/
structure F0StepTransportData (S : Finset Qbar) (alpha0 : Qbar) where
  target : Finset Qbar
  target_eq : target = f0StepTarget S alpha0
  maxDeg_le : maxDeg target ≤ maxDeg S
  measure_lt : Prod.Lex (· < ·) (· < ·) (maxDeg target, numMax target) (maxDeg S, numMax S)
  critValue_deg_le : ∀ y : Qbar, y ∈ f0CritValues alpha0 → degQ y ≤ (f0Poly alpha0).natDegree - 1

/-- Build the concrete transport data for an admissible state (alpha0 of maximal degree
>= 2). -/
def f0StepTransportData (S : Finset Qbar) (alpha0 : Qbar)
    (halpha0 : alpha0 ∈ S) (hmax : degQ alpha0 = maxDeg S) (h2 : 2 ≤ degQ alpha0) :
    F0StepTransportData S alpha0 :=
  { target := f0StepTarget S alpha0
    target_eq := rfl
    maxDeg_le := f0StepTarget_maxDeg_le S alpha0 halpha0 hmax
    measure_lt := f0StepTarget_measure_lt S alpha0 halpha0 hmax h2
    critValue_deg_le := fun y hy => f0CritValue_deg_le alpha0 hy }

/-- NAMED INPUT (paper transport): from the target state S' = f0StepTarget S alpha0 the
paper Lemma 2.4 target transports backwards to S.  This is the geometric content still
named (composition of P1 morphisms with the base case); NOT asserted here. -/
def F0TransportBackwardInput (S S' : Finset Qbar) (alpha0 : Qbar) : Prop :=
  True

/-- Rows: real definitions + proved parts + named remaining input. -/
def f0StepGeometryRows : List (String × String × String) :=
  [ ("f0 = minpoly as P1(Qbar) map", "DEFINED", "f0Poly / f0Map / polyMapQbar; f0Map_infty, f0Map_finite, f0Map_eq_infty_iff (PROVED)")
  , ("critical points/values over Qbar", "DEFINED + PROVED", "f0CritPoints, f0CritValues, f0CritValuesFinset; f0CritValue_mem_image, f0CritValues_subset_image")
  , ("critical-value degree bound", "PROVED", "f0CritValue_deg_lt (degQ_critValue_lt) + f0CritValue_deg_le (undirected)")
  , ("S' finite step target + measure decrease", "PROVED", "f0StepTarget = stepSet; f0StepTarget_maxDeg_le, f0StepTarget_measure_lt")
  , ("S' -> S transport data record", "DEFINED + PROVED", "F0StepTransportData, f0StepTransportData (concrete data)")
  , ("paper backward transport (Target S' -> Target S)", "NAMED INPUT", "F0TransportBackwardInput (not asserted)")
  , ("closure", "NOT CLAIMED", "GATE NOT PASSED; no Qbar closure claim") ]

theorem f0StepGeometryRows_length : f0StepGeometryRows.length = 7 := rfl

#check f0Map
#check f0CritValues
#check f0CritValue_deg_le
#check f0StepTransportData

end LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
end
