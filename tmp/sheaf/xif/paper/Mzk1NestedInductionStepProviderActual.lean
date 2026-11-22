import Mathlib
import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.PaperScopeLemma24Actual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NestedInductionStepProviderActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

abbrev F : Type := AlgebraicClosure ℚ

local instance : DecidableEq F := Classical.decEq F
local instance : DecidableEq (P1Point F) := Classical.decEq _

/-- The point map of a polynomial over F on P1(F). -/
def f0Map (q : Polynomial F) : P1Point F → P1Point F := polyEvalP1K q

/-- Composition of the point maps of two polynomials. -/
theorem f0Map_comp (q r : Polynomial F) (p : P1Point F) :
    f0Map (r.comp q) p = f0Map r (f0Map q p) := by
  cases p with
  | none => rfl
  | some x => simp [f0Map, polyEvalP1K, Polynomial.eval_comp]

/-- Evaluation and aeval agree on coefficients in F itself. -/
theorem eval_eq_aeval_self (p : Polynomial F) (w : F) :
    Polynomial.eval w p = Polynomial.aeval w p := by
  simp [Polynomial.aeval_def]

/-- One step set at P1 level: S' = f0(S) union f0(critical points of f0). -/
def stepSetP (S : Finset (P1Point F)) (q : Polynomial F) : Finset (P1Point F) :=
  (S.image (f0Map q)) ∪
    (((Polynomial.derivative q).aroots F).toFinset.image
      (fun z => P1Point.ofFinite (Polynomial.aeval z q)))

/-- **CV composition law over F (named input)**: a critical point of a composite is a
critical point of the inner factor or maps to a critical point of the outer factor
(the F-level, point form of the critical-value composition law). -/
def CVCompositionLawF : Prop :=
  ∀ (q r : Polynomial F) (z : F),
    Polynomial.aeval z (Polynomial.derivative (r.comp q)) = 0 →
      Polynomial.aeval z (Polynomial.derivative q) = 0 ∨
        Polynomial.aeval (Polynomial.aeval z q) (Polynomial.derivative r) = 0

/-- **Target transport (minpoly side, PROVED conditionally on the CV composition law):
if the paper-scope target holds at the image state S' with parameter beta' = f0(beta),
then it holds at (S, beta): compose the witness polynomial with f0, using that f0(S) is
contained in S' and that the critical values of f0 lie in S'. -/
theorem stepTransport_of_goal (hcv : CVCompositionLawF)
    {S : Finset (P1Point F)} {beta : P1Point F} {q : Polynomial F}
    {S' : Finset (P1Point F)}
    (hqpos : 0 < q.natDegree)
    (hmap : ∀ p ∈ S, f0Map q p ∈ S')
    (hcvS : ∀ z : F, Polynomial.aeval z (Polynomial.derivative q) = 0 →
      P1Point.ofFinite (Polynomial.aeval z q) ∈ S')
    (hgoal : PaperScopeLemma24Target S' (f0Map q beta)) :
    PaperScopeLemma24Target S beta := by
  obtain ⟨Sphi, r, hdeg, hmaps, hbeta, hcrit⟩ := hgoal
  refine ⟨Sphi, r.comp q, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_comp]
    exact Nat.mul_pos hdeg hqpos
  · intro p hp
    obtain ⟨rho, hrho, hval⟩ := hmaps _ (hmap p hp)
    refine ⟨rho, hrho, ?_⟩
    change f0Map (r.comp q) p = castRatPoint rho
    rw [f0Map_comp]
    exact hval
  · rintro ⟨rho, hrho, hval⟩
    apply hbeta
    refine ⟨rho, hrho, ?_⟩
    change f0Map (r.comp q) beta = castRatPoint rho at hval
    rw [f0Map_comp] at hval
    exact hval
  · intro z hz
    have hcomp : Polynomial.aeval z (r.comp q) = Polynomial.aeval (Polynomial.aeval z q) r :=
      Polynomial.aeval_comp z
    rcases hcv q r z hz with hinner | houter
    · obtain ⟨rho, hrho, hval⟩ := hmaps _ (hcvS z hinner)
      refine ⟨rho, hrho, ?_⟩
      rw [hcomp]
      change castRatPoint rho = P1Point.ofFinite (Polynomial.aeval (Polynomial.aeval z q) r)
      rw [← eval_eq_aeval_self r (Polynomial.aeval z q)]
      have hval' : castRatPoint rho =
          P1Point.ofFinite (Polynomial.eval (Polynomial.aeval z q) r) := by
        rw [← hval]
        rfl
      exact hval'
    · obtain ⟨rho, hrho, hval⟩ := hcrit (Polynomial.aeval z q) houter
      refine ⟨rho, hrho, ?_⟩
      rw [hcomp]
      exact hval

/-- Status: minpoly side of the StepProvider (P1 step set, point-map composition, target
transport along f0) PROVED conditionally on the CV composition law over F; the geometric
existence of the normalised f0 with f0(beta) notin S' remains named (analytic avoidance). -/
def StepProviderMinpolyStatus : Audit.Obligation :=
  { id := "MZK1.problemC.step-provider.minpoly"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 163-206; Lead A411/A414 assignment"
    status := Audit.VerificationStatus.interface
    note := "PROVED (minpoly side): f0Map/polyEvalP1K composition identity f0Map_comp; eval_eq_aeval_self; stepSetP (S' = f0(S) union f0(critical points) at P1 level); stepTransport_of_goal (PaperScopeLemma24Target S' (f0 beta) => PaperScopeLemma24Target S beta by composing with q under hmap : f0(S) subset S' and hcvS : f0(critical values) subset S'; consumes named CVCompositionLawF). NAMED REMAINDER: CVCompositionLawF (F-level point CV composition law; mathematically standard, not yet formalized here) and the geometric normalised f0 construction with f0(beta) notin S' (analytic avoidance layer). No closure; binding HOLD; gate NOT PASSED; registry frozen 14041."
    dependsOn := [ "MZK1.problemC.base-case", "MZK1.problemC.nested-induction" ]
    sorryItems :=
      [ "CVCompositionLawF (F-level point CV composition law; named)",
        "geometric normalised f0 with f0(beta) notin S' (analytic avoidance; named)" ] }

#check stepSetP
#check stepTransport_of_goal
end LeanFormal.IUT.XiFPaper.Mzk1NestedInductionStepProviderActual
end