import Mathlib
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma24BetaAvoidanceActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24ShapeStepActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24BetaAvoidanceActual

local instance : DecidableEq (P1Point ℂ) := Classical.decEq _

/-- **(M) one-step shape, PROVED** (paper [Mzk1] Lemma 2.4 lines 183-206): for a monic
degree-d f0 with coefficient bound C (the (F) bound d0^d0), a finite set S with
|alpha| <= 1, and beta large enough (Lemma 2.3 normalization), the polynomial map f0
gives a nonconstant P^1-morphism (stage4 interface) preserving the finite set into
the target set {infinity} union f0(S), and AVOIDING beta: exactly the paper's
S' = f0(S) with beta outside S'. -/
theorem s3135_f0_step_shape
    (d : Nat) (hd : 1 ≤ d) (C : Real) (hC1 : 1 ≤ C)
    (p : Polynomial ℂ) (hmon : p.Monic) (hdeg : p.natDegree = d)
    (hcoeff : ∀ k, k < d → ‖p.coeff k‖ ≤ C)
    (S : Finset ℂ) (hS : ∀ a ∈ S, ‖a‖ ≤ 1) (β : ℂ) :
    ∃ b : Real, b + C * d ≤ ‖β‖ →
      ∃ (φ : P1Morphism ℂ) (targetSet : Set (P1Point ℂ)),
        φ.nonconstant ∧
          PreservesSet φ ((↑(S.image (P1Point.ofFinite)) : Set (P1Point ℂ))) targetSet ∧
          AvoidsPoint φ (P1Point.ofFinite β) targetSet := by
  classical
  obtain ⟨b, hb⟩ := s3135_beta_avoidance d hd C hC1
  refine ⟨b, ?_⟩
  intro hβ
  let mapPoints : P1Point ℂ → P1Point ℂ := fun z => z.map (fun x => p.eval x)
  let φ : P1Morphism ℂ :=
    { ratFunc := 0
      mapPoints := mapPoints
      nonconstant := 1 ≤ p.natDegree
      nonconstant_proof := by rw [hdeg]; exact hd }
  let targetSet : Set (P1Point ℂ) :=
    {(P1Point.infty : P1Point ℂ)} ∪
      (S.image (fun a => P1Point.ofFinite (p.eval a)) : Set (P1Point ℂ))
  refine ⟨φ, targetSet, ?_, ?_, ?_⟩
  · show 1 ≤ p.natDegree
    rw [hdeg]; exact hd
  · intro z hz
    obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hz
    simp only [φ, mapPoints, P1Point.ofFinite, Option.map_some, targetSet]
    exact Or.inr (Finset.mem_image_of_mem _ haS)
  · intro hmem
    simp only [φ, mapPoints, P1Point.ofFinite, Option.map_some, targetSet] at hmem
    rcases hmem with h | h
    · exact P1Point.ofFinite_ne_infty (p.eval β) h
    · obtain ⟨a, haS, heq⟩ := Finset.mem_image.mp h
      have hval : p.eval β = p.eval a := by simpa using heq.symm
      exact hb p hmon hdeg hcoeff a β (hS a haS) hβ hval

/-- (M) status: the f0-step shape (nonconstant + PreservesSet + AvoidsPoint) is PROVED
from the (F) coefficient bound, the (M1a) monic growth, the (M1b) beta-avoidance and
the stage4 P^1-morphism interface.  Remaining for the full Lemma 2.4 StatementShape:
the UnramifiedOver clause (stage4 unramifiedAt data) and the nested induction/descent
assembly (measure + Mzk1Lemma24MeasureActual + Mzk1Lemma24DescentActual). -/
def s3135Mzk1ShapeStepStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.statement-shape-step"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 183-206"
    status := Audit.VerificationStatus.interface
    note := "PROVED: s3135_f0_step_shape (monic f0, coeffs <= C, |alpha|<=1, beta large => stage4 P1Morphism nonconstant, PreservesSet into {infty} union f0(S), AvoidsPoint beta) consuming (F) Mzk1Lemma24F0BoundActual, (M1a) Mzk1Lemma24GrowthActual, (M1b) Mzk1Lemma24BetaAvoidanceActual, and stage4 Mzk1P1MorphismInterfaceActual. REMAINING: UnramifiedOver clause (stage4 unramifiedAt data interface) and nested (m,d)-induction assembly over the measure (Mzk1Lemma24MeasureActual/DescentActual) to conclude Mzk1Lemma24StatementShape. No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.f0-coefficient-bound", "MZK1.lemma24.p1-interface-application" ]
    sorryItems :=
      [ "UnramifiedOver clause (stage4 unramifiedAt data)",
        "nested (m,d)-induction assembly to Mzk1Lemma24StatementShape" ] }

#check s3135_f0_step_shape
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24ShapeStepActual
end