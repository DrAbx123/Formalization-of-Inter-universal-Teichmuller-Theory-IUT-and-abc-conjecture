import tmp.sheaf.xif.paper.Mzk1CVCompositionFActual
import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeActual

/-! # Mzk1F0StepTransportProvedActual — f5 target transport PROVED (real)

Real Lean (no sorry/axiom): the f5 backward transport of the paper-scope target along the f0
step, formerly the named input F0StepTransportInput, is PROVED from the abc minpoly transport
stepTransport_of_goal_proved (CV-composition law discharged in Mzk1CVCompositionFActual) with
q = minpoly alpha0 lifted to Qbar-coefficients, using the f1/f2 membership lemmas.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1F0StepTransportProvedActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual

abbrev Qb : Type := AlgebraicClosure ℚ

/-- f5 target-transport input (local definition; formerly from the fixed-beta wrapper file). -/
def F0StepTransportInput : Prop :=
  forall (S : Finset (P1Point Qbar)) (beta : P1Point Qbar) (alpha0 : Qbar),
    PaperScopeLemma24Target (stepSetP1 S alpha0) (f0Map alpha0 beta) ->
      PaperScopeLemma24Target S beta

/-- Our Q-polynomial f0Map agrees with the abc provider's f0Map at lifted coefficients. -/
theorem f0Map_eq_provider (alpha0 : Qbar) (p : P1Point Qbar) :
    f0Map alpha0 p =
      LeanFormal.IUT.XiFPaper.Mzk1NestedInductionStepProviderActual.f0Map
        ((f0Poly alpha0).map (algebraMap ℚ Qbar)) p := by
  cases p with
  | none => rfl
  | some x =>
      simp [f0Map, polyMapQbar,
        LeanFormal.IUT.XiFPaper.Mzk1NestedInductionStepProviderActual.f0Map,
        polyEvalP1K, f0Poly, Polynomial.eval_map, Polynomial.aeval_def]

/-- Converse membership in the finite critical set from the derivative root equation. -/
theorem mem_critSet_of_aeval_derivative_eq_zero (alpha0 z : Qbar)
    (hz : aeval z (derivative (minpoly ℚ alpha0)) = 0) : z ∈ critSet alpha0 := by
  classical
  have hder : derivative (minpoly ℚ alpha0) ≠ 0 := by
    rw [Polynomial.derivative_ne_zero]
    have hpos : 0 < degQ alpha0 := degQ_pos alpha0
    rw [degQ] at hpos
    omega
  rw [critSet, Multiset.mem_toFinset, Polynomial.mem_aroots]
  exact ⟨hder, hz⟩

/-- **f5 PROVED:** backward transport of the paper-scope 2.4 target along the f0 step. -/
theorem f0StepTransportInput_proved : F0StepTransportInput := by
  intro S beta alpha0 hgoal
  let q : Polynomial Qb := (f0Poly alpha0).map (algebraMap ℚ Qb)
  have hqpos : 0 < q.natDegree := by
    have hdeg : q.natDegree = degQ alpha0 := by
      dsimp only [q]
      rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ Qb).injective]
      rfl
    rw [hdeg]
    exact degQ_pos alpha0
  have hmap : ∀ p ∈ S,
      LeanFormal.IUT.XiFPaper.Mzk1NestedInductionStepProviderActual.f0Map q p ∈
        stepSetP1 S alpha0 := by
    intro p hp
    rw [← f0Map_eq_provider alpha0 p]
    exact mem_stepSetP1_of_mem hp
  have hcvS : ∀ z : Qb,
      Polynomial.aeval z (Polynomial.derivative q) = 0 →
        P1Point.ofFinite (Polynomial.aeval z q) ∈ stepSetP1 S alpha0 := by
    intro z hz
    have hz' : aeval z (derivative (minpoly ℚ alpha0)) = 0 := by
      have hd : Polynomial.derivative q =
          (Polynomial.derivative (f0Poly alpha0)).map (algebraMap ℚ Qb) := by
        dsimp only [q]
        rw [Polynomial.derivative_map]
      rw [hd] at hz
      simpa [f0Poly, Polynomial.aeval_def, Polynomial.eval_map_algebraMap] using hz
    have heq : Polynomial.aeval z q = aeval z (minpoly ℚ alpha0) := by
      dsimp only [q]
      simp [f0Poly, Polynomial.aeval_def, Polynomial.eval_map_algebraMap]
    have hmem := mem_stepSetP1_of_crit (S := S) (alpha0 := alpha0)
      (mem_critSet_of_aeval_derivative_eq_zero alpha0 z hz')
    rw [heq]
    exact hmem
  have hgoal' : PaperScopeLemma24Target (stepSetP1 S alpha0)
      (LeanFormal.IUT.XiFPaper.Mzk1NestedInductionStepProviderActual.f0Map q beta) := by
    rw [← f0Map_eq_provider alpha0 beta]
    exact hgoal
  exact LeanFormal.IUT.XiFPaper.Mzk1CVCompositionFActual.stepTransport_of_goal_proved
    (S := S) (beta := beta) (q := q) (S' := stepSetP1 S alpha0) hqpos hmap hcvS hgoal'

#check f0StepTransportInput_proved

end LeanFormal.IUT.XiFPaper.Mzk1F0StepTransportProvedActual
end
