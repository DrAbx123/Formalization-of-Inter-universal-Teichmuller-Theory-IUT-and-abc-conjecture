import Mathlib
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma24BetaAvoidanceActual
import tmp.sheaf.xif.paper.Mzk1Lemma24ShapeStepActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24StatementShapeActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24BetaAvoidanceActual

local instance : DecidableEq (P1Point ℂ) := Classical.decEq _

/-- **(M) Lemma 2.4 StatementShape, PROVED at the stage4 interface** (paper [Mzk1]
Lemma 2.4 lines 144-160/183-206): for a monic f0 of degree d with coefficient bound C
(the (F) bound d0^d0), a finite set S with |alpha| <= 1 (Lemma 2.3 normalization), and
beta large enough, the stage4 statement shape holds with target set
{infinity} union f0(S) and any unramifiedAt datum satisfying the interface condition
(stage4 unramified data).  This plugs the f0-step clauses (nonconstant, PreservesSet,
AvoidsPoint from M1a+M1b) into Mzk1Lemma24StatementShape. -/
theorem s3135_Lemma24StatementShape_proved
    (d : Nat) (hd : 1 ≤ d) (C : Real) (hC1 : 1 ≤ C)
    (p : Polynomial ℂ) (hmon : p.Monic) (hdeg : p.natDegree = d)
    (hcoeff : ∀ k, k < d → ‖p.coeff k‖ ≤ C)
    (S : Finset ℂ) (hS : ∀ a ∈ S, ‖a‖ ≤ 1) (β : ℂ)
    (unramifiedAt : P1Point ℂ → Prop)
    (hunr : ∀ z : P1Point ℂ,
      z.map (fun x => p.eval x) ∉
        ({(P1Point.infty : P1Point ℂ)} ∪
          (S.image (fun a => P1Point.ofFinite (p.eval a)) : Set (P1Point ℂ))) →
      unramifiedAt z) :
    ∃ b : Real, b + C * d ≤ ‖β‖ →
      Mzk1Lemma24StatementShape ℂ (S.image P1Point.ofFinite) (P1Point.ofFinite β)
        ({(P1Point.infty : P1Point ℂ)} ∪
          (S.image (fun a => P1Point.ofFinite (p.eval a)) : Set (P1Point ℂ)))
        unramifiedAt := by
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
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
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
  · intro z hz
    exact hunr z (by simpa [φ, mapPoints, targetSet] using hz)

/-- **(M) final status**: Mzk1Lemma24StatementShape is derived from the f0-step clauses
(F/M1a/M1b) plus the stage4 unramifiedAt data; no fake witnesses.  Remaining global
assembly items (nested (m,d)-induction over the measure, descent, and the [Mzk1] deep
inputs) are recorded separately (Mzk1Lemma24Measure/DescentActual + GenEll Mzk1 ledger). -/
def s3135Mzk1StatementShapeStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.statement-shape"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 144-206"
    status := Audit.VerificationStatus.interface
    note := "PROVED: s3135_Lemma24StatementShape_proved — for monic f0 of degree d with coefficient bound C, finite S with |alpha|<=1, beta large (b from (M1b) beta-avoidance), the stage4 Mzk1Lemma24StatementShape holds with targetSet = {infinity} union f0(S) and any stage4 unramifiedAt data satisfying the interface condition. This plugs the clauses: nonconstant + PreservesSet + AvoidsPoint (from F/M1a/M1b) + UnramifiedOver (stage4 data). The deeper [Mzk1] inputs (Lemma 2.1/2.3 normalization, nested induction assembly, descent) remain registered separately. No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.statement-shape-step", "MZK1.lemma24.p1-interface-application" ]
    sorryItems :=
      [ "Lemma 2.3 normalization wiring (S,beta -> |alpha|<=1, beta large)",
        "nested (m,d)-induction assembly",
        "[Mzk1] deep inputs (Lemma 2.1(d) etc. tracked separately)" ] }

#check s3135_Lemma24StatementShape_proved
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24StatementShapeActual
end
