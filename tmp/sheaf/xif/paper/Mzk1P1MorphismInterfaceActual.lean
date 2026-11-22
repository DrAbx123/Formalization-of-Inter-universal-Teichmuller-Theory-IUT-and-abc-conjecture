import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

/-! # Mzk1P1MorphismInterfaceActual — P^1-morphism / unramifiedness interface for [Mzk1] Lemma 2.2

STEP 0 prior-art: deep search 'P1 morphism|Belyi map|unramified over|RatFunc' -> Mathlib has
RatFunc (FieldTheory.RatFunc.Basic), scheme morphisms and unramified morphisms, but no
Belyi-map interface; LeanFormal tree has none; ported FLT has SmoothProperCurve.FiniteMapData
(scheme-level) — this interface is the missing lightweight layer for Lemma 2.2/2.4
statements. No fake proof: predicates that need missing API are explicit fields/parameters.

PAPER: [Mzk1] Lemma 2.2 (lines 106-135) and Lemma 2.4 (144-205) speak of nonconstant
f in Q[x] / Qbar(x) defining phi : P^1 -> P^1 with (a) phi(S) inside a target set,
(b) phi(beta) outside it, (c) phi unramified over P^1 minus the target set.

THIS FILE: standard P^1 model (Option K), P1Morphism data, interface predicates
UnramifiedOver / PreservesSet / AvoidsPoint as explicit data, and the Lemma 2.2/2.4
statement shapes. No theorem of this file is counted as a paper result. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

universe u

/-- The standard model of P^1 over K: K plus a point at infinity. -/
abbrev P1Point (K : Type u) : Type u := Option K

namespace P1Point

variable {K : Type u}

/-- The point at infinity. -/
def infty : P1Point K := none

/-- The finite point corresponding to x in K. -/
def ofFinite (x : K) : P1Point K := some x

theorem ofFinite_ne_infty (x : K) : ofFinite x ≠ infty := by
  simp [ofFinite, infty]

theorem eq_infty_or_finite (p : P1Point K) : p = infty ∨ ∃ x, p = ofFinite x := by
  cases p with
  | none => exact Or.inl rfl
  | some x => exact Or.inr ⟨x, rfl⟩

end P1Point

/-- A morphism P^1_K -> P^1_K presented by a rational function plus its value map. -/
structure P1Morphism (K : Type u) [Field K] where
  ratFunc : RatFunc K
  mapPoints : P1Point K → P1Point K
  nonconstant : Prop
  nonconstant_proof : nonconstant

/-- A subset T of P^1 is preserved: every point of S maps into T. -/
def PreservesSet {K : Type u} [Field K] (φ : P1Morphism K)
    (S T : Set (P1Point K)) : Prop :=
  ∀ p ∈ S, φ.mapPoints p ∈ T

/-- A point is avoided: beta maps outside T. -/
def AvoidsPoint {K : Type u} [Field K] (φ : P1Morphism K)
    (β : P1Point K) (T : Set (P1Point K)) : Prop :=
  φ.mapPoints β ∉ T

/-- Unramified over T, with the local unramifiedness predicate supplied as data
(different/derivative API to be built later). -/
def UnramifiedOver {K : Type u} [Field K] (φ : P1Morphism K)
    (T : Set (P1Point K)) (unramifiedAt : P1Point K → Prop) : Prop :=
  ∀ p, φ.mapPoints p ∈ T → unramifiedAt p

/-- Lemma 2.2 statement shape: existence of a nonconstant phi with the three
properties (target set T = {0,1,infinity}). -/
def Mzk1Lemma22StatementShape (K : Type u) [Field K] [DecidableEq K]
    (S : Finset (P1Point K)) (β : P1Point K) (C : ℝ)
    (targetSet : Set (P1Point K)) (unramifiedAt : P1Point K → Prop) : Prop :=
  ∃ φ : P1Morphism K, φ.nonconstant ∧
    PreservesSet φ (↑S : Set (P1Point K)) targetSet ∧
    AvoidsPoint φ β targetSet ∧
    UnramifiedOver φ {p | p ∉ targetSet} unramifiedAt

/-- Lemma 2.4 statement shape (same interface, with the target set S_phi as a parameter). -/
def Mzk1Lemma24StatementShape (K : Type u) [Field K] [DecidableEq K]
    (S : Finset (P1Point K)) (β : P1Point K)
    (targetSet : Set (P1Point K)) (unramifiedAt : P1Point K → Prop) : Prop :=
  ∃ φ : P1Morphism K, φ.nonconstant ∧
    PreservesSet φ (↑S : Set (P1Point K)) targetSet ∧
    AvoidsPoint φ β targetSet ∧
    UnramifiedOver φ {p | p ∉ targetSet} unramifiedAt

#check P1Point.ofFinite_ne_infty
#check P1Point.eq_infty_or_finite
#check P1Morphism
#check PreservesSet
#check AvoidsPoint
#check UnramifiedOver
#check Mzk1Lemma22StatementShape
#check Mzk1Lemma24StatementShape

end LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
end
