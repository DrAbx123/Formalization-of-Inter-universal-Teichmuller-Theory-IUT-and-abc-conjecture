import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import Mathlib.Tactic

/-! # Mzk1Lemma22CompositionActual — [Mzk1] Lemma 2.2 induction: P1Morphism composition + step schema

STEP 0 prior-art: corpus Lemma 2.2 lines 106-135 (induction on |S|, composing morphisms
P^1 -> P^1); Mzk1P1MorphismInterfaceActual (P1Point/P1Morphism/PreservesSet/AvoidsPoint/
UnramifiedOver/Lemma22StatementShape); Mzk1Lemma21dAssemblyActual (Lemma 2.1(a)-(d) all
proved).  This file supplies the composition layer and the induction-step schema; the
per-step construction (f+f0 from Lemma 2.1 with |S'|<|S|) is the recorded obligation. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22CompositionActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open Polynomial

universe u

variable {K : Type u} [Field K]

/-- Composition of P^1-morphisms (second map applied after the first); the nonconstancy
of the second component is an explicit hypothesis.

The rational function is the true substitution ψ∘φ (NOT the product): write
ψ = a/b, φ = c/d; substituting φ into the polynomial a gives
Polynomial.aeval φ.ratFunc a (and likewise b), then divide.  For nonconstant φ the
denominator is nonzero (a nonconstant rational function is transcendental over K), so
this represents the same function as mapPoints. -/
noncomputable def comp (φ ψ : P1Morphism K) (hψ : ψ.nonconstant) : P1Morphism K where
  ratFunc :=
    (Polynomial.aeval φ.ratFunc ψ.ratFunc.num) /
      (Polynomial.aeval φ.ratFunc ψ.ratFunc.denom)
  mapPoints := fun p => ψ.mapPoints (φ.mapPoints p)
  nonconstant := ψ.nonconstant
  nonconstant_proof := hψ

/-- Preservation composes. -/
theorem PreservesSet_comp {φ ψ : P1Morphism K} {S T U : Set (P1Point K)}
    (hφ : PreservesSet φ S T) (hψ : PreservesSet ψ T U) (hψ_nc : ψ.nonconstant) :
    PreservesSet (comp φ ψ hψ_nc) S U := by
  intro p hp
  exact hψ (φ.mapPoints p) (hφ p hp)

/-- Avoidance composes. -/
theorem AvoidsPoint_comp {φ ψ : P1Morphism K} {β : P1Point K} {T U : Set (P1Point K)}
    (hφ : AvoidsPoint φ β T) (hψ : AvoidsPoint ψ (φ.mapPoints β) U) (hψ_nc : ψ.nonconstant) :
    AvoidsPoint (comp φ ψ hψ_nc) β U := by
  intro hmem
  exact hψ hmem

/-- Unramifiedness composes when the second map maps the complement of the incoming
target set into the incoming target set (preimage condition). -/
theorem UnramifiedOver_comp {φ ψ : P1Morphism K} {T U : Set (P1Point K)}
    {u₁ u₂ : P1Point K → Prop}
    (hφ : UnramifiedOver φ T u₁) (hψ : UnramifiedOver ψ U u₂)
    (hpre : ∀ q, ψ.mapPoints q ∈ U → q ∈ T) (hψ_nc : ψ.nonconstant) :
    UnramifiedOver (comp φ ψ hψ_nc) U (fun p => u₁ p ∧ u₂ (φ.mapPoints p)) := by
  intro p hp
  have h2 : u₂ (φ.mapPoints p) := hψ (φ.mapPoints p) hp
  have h1 : u₁ p := hφ p (hpre (φ.mapPoints p) hp)
  exact ⟨h1, h2⟩

/-- One induction step of Lemma 2.2: a nonconstant morphism reducing (S,beta) to a
smaller (S',beta') while preserving the target set and avoiding beta. -/
structure Mzk1Lemma22InductionStep (K : Type u) [Field K] [DecidableEq K] where
  source : Finset (P1Point K)
  targetS : Finset (P1Point K)
  beta : P1Point K
  beta' : P1Point K
  phi : P1Morphism K
  targetSet : Set (P1Point K)
  unramifiedAt : P1Point K → Prop
  card_lt : targetS.card < source.card
  preserves : PreservesSet phi (↑source : Set (P1Point K)) targetSet
  avoids : AvoidsPoint phi beta targetSet
  beta'_eq : beta' = phi.mapPoints beta
  unramified : UnramifiedOver phi {p | p ∉ targetSet} unramifiedAt

/-- Composition assembly of one step: an induction hypothesis morphism for (S',beta')
composes with the step to give a witness for (S,beta) preserving the final target and
avoiding beta (unramifiedness composition handled by UnramifiedOver_comp with the
preimage hypothesis; recorded separately). -/
theorem mzk1Lemma22_comp_witness [DecidableEq K] {C : ℝ}
    (step : Mzk1Lemma22InductionStep K)
    (finalTarget : Set (P1Point K))
    (htarget : step.targetSet = (↑step.targetS : Set (P1Point K)))
    (hψ : Mzk1Lemma22StatementShape K step.targetS step.beta' C finalTarget
      (fun _ => True)) :
    ∃ φ : P1Morphism K, φ.nonconstant ∧
      PreservesSet φ (↑step.source : Set (P1Point K)) finalTarget ∧
      AvoidsPoint φ step.beta finalTarget := by
  obtain ⟨ψ, hψnc, hpres, hav, _hunr⟩ := hψ
  refine ⟨comp step.phi ψ hψnc, hψnc, ?_, ?_⟩
  · have hpres' : PreservesSet ψ step.targetSet finalTarget := by
      rw [htarget]
      exact hpres
    exact PreservesSet_comp step.preserves hpres' hψnc
  · show ψ.mapPoints (step.phi.mapPoints step.beta) ∉ finalTarget
    rw [← step.beta'_eq]
    exact hav

/-- Obligation rows for the full Lemma 2.2 induction (each recorded, not faked). -/
structure Mzk1Lemma22ObligationRow where
  item : String
  status : String
  proved : Bool

def mzk1Lemma22InductionObligations : List Mzk1Lemma22ObligationRow :=
  [ ⟨"P1Morphism composition + PreservesSet/AvoidsPoint composition", "PROVED (this file)", true⟩,
    ⟨"UnramifiedOver composition (with preimage hypothesis)", "PROVED (this file)", true⟩,
    ⟨"step construction from Lemma 2.1: lambda*S, f+f0, |S'|<|S|", "PENDING (needs polynomial-map evaluation and cardinality collapse proof)", false⟩,
    ⟨"induction on |S| + base case (uses card_lt + mzk1Lemma22_comp_witness)", "PENDING", false⟩,
    ⟨"rational-coefficient descent for the resulting f in Q[x]", "PENDING", false⟩ ]

theorem mzk1Lemma22InductionObligations_length :
    mzk1Lemma22InductionObligations.length = 5 := rfl

#check comp
#check PreservesSet_comp
#check AvoidsPoint_comp
#check UnramifiedOver_comp
#check Mzk1Lemma22InductionStep
#check mzk1Lemma22_comp_witness
#check mzk1Lemma22InductionObligations_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22CompositionActual
end
