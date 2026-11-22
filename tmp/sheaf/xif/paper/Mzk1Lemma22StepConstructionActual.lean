import tmp.sheaf.xif.paper.Mzk1PolyMapActual
import tmp.sheaf.xif.paper.Mzk1Lemma22CompositionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1Lemma22StepConstructionActual — [Mzk1] Lemma 2.2 (b) STEP CONSTRUCTION

STEP 0 prior-art (reuse, no re-proof): corpus [Mzk1] Lemma 2.1 (properties (a)-(d),
~lines 35-105: f(x)=x^m(x-1)^n, r=m/(m+n), f0=-min f) and Lemma 2.2 statement/proof
(lines 106-135: induction on |S|, apply Lemma 2.1 [C=2] to lambda*S, f+f0);
stage4 tooling: Mzk1P1MorphismInterfaceActual (P1Point/P1Morphism/PreservesSet/
AvoidsPoint/UnramifiedOver/Mzk1Lemma22StatementShape), Mzk1Lemma22CompositionActual
(comp/…/Mzk1Lemma22InductionStep/mzk1Lemma22_comp_witness PROVED), Mzk1PolyMapActual
(polyMapPoints/polyMorphism/specialSet/polyUnramifiedAt PROVED).  Mathlib:
Finset.card_image_iff / card_image_le.

THIS FILE: the per-step construction of Lemma 2.2 from Lemma 2.1 data, on the
stage4 polynomial interface (K = ℚ):
* card_image_lt_of_not_injOn / card_image_lt_of_collision (A-class cardinal collapse);
* lemma22Step_card_lt: |phi(S)| < |S| when 0,1 in S and g(0)=g(1) (the Lemma 2.1
  polynomial g = x^m(x-1)^n + f0 has g(0)=g(1)=f0, so 0,1 collapse);
* lemma22StepOfData / lemma22StepOfPoly: build the exact
  Mzk1Lemma22InductionStep ℚ with phi := polyMorphism g hdeg, source := S,
  targetS := S.image (polyMapPoints g), beta' := polyMorphism g hdeg applied to beta,
  targetSet := ↑targetS, htarget rfl; consumes the Lemma 2.1 conclusion data
  (preserves/avoids/unramified) as explicit hypotheses;
* lemma22Step_exists: the step-existence statement stage4 wires into its strong
  induction: ∃ step : Mzk1Lemma22InductionStep ℚ, step.source = S ∧ step.beta = β ∧
  step.targetS = S.image (polyMapPoints g) ∧ step.beta' = polyMapPoints g β ∧
  step.phi = polyMorphism g hdeg;
* lemma22Step_compose: reuse stage4's mzk1Lemma22_comp_witness.

HONEST SCOPE: the paper's remaining per-step inputs — Lemma 2.1 (a) phi(S) in
target, (c) phi(beta) outside target, (b) unramifiedness over the complement, and the
lambda*S/f0 normalization encoding g = f+f0 — are consumed as explicit hypotheses;
this file constructs the STEP and its cardinal collapse and does not reprove Lemma 2.1
(Mzk1Lemma21dAssemblyActual) nor the full induction (stage4 files).  No closure claim.
Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepConstructionActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22CompositionActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual

universe u

variable {K : Type u} [Field K] [DecidableEq K]

/-- **Cardinal collapse from non-injectivity (A-class):** if the map is not injective
on a finite source, the image has strictly smaller cardinality. -/
theorem card_image_lt_of_not_injOn {α β : Type*} [DecidableEq β] (s : Finset α)
    (f : α → β) (h : ¬ Set.InjOn f (↑s : Set α)) :
    (s.image f).card < s.card := by
  have hle : (s.image f).card ≤ s.card := Finset.card_image_le
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd (Finset.card_image_iff.mp heq) h

/-- **Cardinal collapse from a collision:** two distinct source points with the same
image give strict decrease (the Lemma 2.2 STEP's |S'| < |S| mechanism). -/
theorem card_image_lt_of_collision (s : Finset (P1Point K)) (f : P1Point K → P1Point K)
    {a b : P1Point K} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hcol : f a = f b) : (s.image f).card < s.card :=
  card_image_lt_of_not_injOn s f (by
    intro hinj
    exact hab (hinj ha hb hcol))

/-- Distinct finite points 0 and 1 of P^1. -/
theorem p1_zero_ne_one : P1Point.ofFinite (0 : ℚ) ≠ P1Point.ofFinite (1 : ℚ) := by
  intro h
  exact zero_ne_one (Option.some.inj h)

/-- **Lemma 2.2 STEP cardinal collapse (the main risk, proved):** if the source set S
contains the distinct points 0 and 1, and the Lemma 2.1 polynomial g satisfies
g(0) = g(1) (for g = x^m(x-1)^n + f0 both sides equal f0), then the image of S under
the P^1-polynomial map has strictly smaller cardinality. -/
theorem lemma22Step_card_lt (S : Finset (P1Point ℚ)) (g : ℚ[X])
    (h0 : P1Point.ofFinite (0 : ℚ) ∈ S) (h1 : P1Point.ofFinite (1 : ℚ) ∈ S)
    (hcol : g.eval 0 = g.eval 1) :
    (S.image (polyMapPoints g)).card < S.card := by
  have hcolP : polyMapPoints g (P1Point.ofFinite (0 : ℚ)) =
      polyMapPoints g (P1Point.ofFinite (1 : ℚ)) := by
    rw [polyMapPoints_finite, polyMapPoints_finite, hcol]
  exact card_image_lt_of_collision S (polyMapPoints g) h0 h1 p1_zero_ne_one hcolP

/-- **STEP construction from Lemma 2.1 data (generic field K):** given the source S,
the Lemma 2.1 morphism phi, beta and target data plus the strict cardinal decrease and
the Lemma 2.1 (a)(b)(c) conclusions, build the induction step with target S' = phi(S)
and beta' = phi(beta). -/
def lemma22StepOfData (S : Finset (P1Point K)) (φ : P1Morphism K)
    (β : P1Point K) (targetSet : Set (P1Point K))
    (unramifiedAt : P1Point K → Prop)
    (card_lt : (S.image φ.mapPoints).card < S.card)
    (preserves : PreservesSet φ (↑S : Set (P1Point K)) targetSet)
    (avoids : AvoidsPoint φ β targetSet)
    (unramified : UnramifiedOver φ {p | p ∉ targetSet} unramifiedAt) :
    Mzk1Lemma22InductionStep K where
  source := S
  targetS := S.image φ.mapPoints
  beta := β
  beta' := φ.mapPoints β
  phi := φ
  targetSet := targetSet
  unramifiedAt := unramifiedAt
  card_lt := card_lt
  preserves := by
    intro p hp
    exact preserves p hp
  avoids := avoids
  beta'_eq := rfl
  unramified := unramified

/-- **The stage4 step object in the polynomial model (K = ℚ):** phi := polyMorphism g
hdeg, source := S, targetS := S.image (polyMapPoints g), targetSet := ↑targetS,
beta' := phi(beta) = some(g.eval beta), card_lt PROVED from the 0/1 collapse,
preserves := image membership, avoids/unramified consumed as explicit data. -/
def lemma22StepOfPoly (S : Finset (P1Point ℚ)) (g : ℚ[X]) (hdeg : 1 ≤ g.natDegree)
    (β : P1Point ℚ)
    (h0 : P1Point.ofFinite (0 : ℚ) ∈ S) (h1 : P1Point.ofFinite (1 : ℚ) ∈ S)
    (hcol : g.eval 0 = g.eval 1)
    (avoids : AvoidsPoint (polyMorphism g hdeg) β
      (↑(S.image (polyMapPoints g)) : Set (P1Point ℚ)))
    (unramified : UnramifiedOver (polyMorphism g hdeg)
      {p | p ∉ (↑(S.image (polyMapPoints g)) : Set (P1Point ℚ))}
      (polyUnramifiedAt g)) :
    Mzk1Lemma22InductionStep ℚ :=
  lemma22StepOfData S (polyMorphism g hdeg) β
    (↑(S.image (polyMapPoints g)) : Set (P1Point ℚ)) (polyUnramifiedAt g)
    (lemma22Step_card_lt S g h0 h1 hcol)
    (by
      intro p hp
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hp))
    avoids unramified

/-- **STEP-EXISTENCE statement for stage4's strong induction:** from Lemma 2.2 point
conditions (0,1 in S; 0 and 1 collapse under g = the Lemma 2.1 polynomial) and the
Lemma 2.1 conclusion data, there is an induction step with exactly
source := S, targetS := S.image (polyMapPoints g), beta' = phi(beta),
phi := polyMorphism g hdeg, targetSet := ↑targetS (htarget rfl downstream). -/
theorem lemma22Step_exists (S : Finset (P1Point ℚ)) (g : ℚ[X]) (hdeg : 1 ≤ g.natDegree)
    (β : P1Point ℚ)
    (h0 : P1Point.ofFinite (0 : ℚ) ∈ S) (h1 : P1Point.ofFinite (1 : ℚ) ∈ S)
    (hcol : g.eval 0 = g.eval 1)
    (avoids : AvoidsPoint (polyMorphism g hdeg) β
      (↑(S.image (polyMapPoints g)) : Set (P1Point ℚ)))
    (unramified : UnramifiedOver (polyMorphism g hdeg)
      {p | p ∉ (↑(S.image (polyMapPoints g)) : Set (P1Point ℚ))}
      (polyUnramifiedAt g)) :
    ∃ step : Mzk1Lemma22InductionStep ℚ,
      step.source = S ∧ step.beta = β ∧
      step.targetS = S.image (polyMapPoints g) ∧
      step.beta' = polyMapPoints g β ∧
      step.phi = polyMorphism g hdeg ∧
      step.targetSet = (↑step.targetS : Set (P1Point ℚ)) := by
  refine ⟨lemma22StepOfPoly S g hdeg β h0 h1 hcol avoids unramified, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **PACKAGED step-existence for stage4's induction** (requested exact shape):
from Lemma 2.2 point conditions (3 < |S|, 0 and 1 in S collapsing under the Lemma 2.1
polynomial g) and the Lemma 2.1 conclusion data, there is a step with source = S,
beta = beta and targetSet = ↑targetS (htarget rfl available).  This is the
existential-abstract form of lemma22StepOfPoly that stage4's stepExists hypothesis
consumes. -/
theorem lemma22StepExists_packaged (S : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (hcard : 3 < S.card)
    (g : ℚ[X]) (hdeg : 1 ≤ g.natDegree)
    (h0 : P1Point.ofFinite (0 : ℚ) ∈ S) (h1 : P1Point.ofFinite (1 : ℚ) ∈ S)
    (hcol : g.eval 0 = g.eval 1)
    (avoids : AvoidsPoint (polyMorphism g hdeg) β
      (↑(S.image (polyMapPoints g)) : Set (P1Point ℚ)))
    (unramified : UnramifiedOver (polyMorphism g hdeg)
      {p | p ∉ (↑(S.image (polyMapPoints g)) : Set (P1Point ℚ))}
      (polyUnramifiedAt g)) :
    ∃ st : Mzk1Lemma22InductionStep ℚ,
      st.source = S ∧ st.beta = β ∧
      st.targetSet = (↑st.targetS : Set (P1Point ℚ)) :=
  ⟨lemma22StepOfPoly S g hdeg β h0 h1 hcol avoids unramified, rfl, rfl, rfl⟩

/-- **Composition consumer (reuse of stage4's proved witness):** a STEP composed with
the induction-hypothesis morphism for (S', beta') yields a nonconstant morphism
preserving the final target and avoiding beta — the Lemma 2.2 induction composition. -/
theorem lemma22Step_compose [DecidableEq K] {C : ℝ} (step : Mzk1Lemma22InductionStep K)
    (finalTarget : Set (P1Point K))
    (htarget : step.targetSet = (↑step.targetS : Set (P1Point K)))
    (hψ : Mzk1Lemma22StatementShape K step.targetS step.beta' C finalTarget
      (fun _ => True)) :
    ∃ φ : P1Morphism K, φ.nonconstant ∧
      PreservesSet φ (↑step.source : Set (P1Point K)) finalTarget ∧
      AvoidsPoint φ step.beta finalTarget :=
  mzk1Lemma22_comp_witness step finalTarget htarget hψ

/-- STEP construction obligations (data: paper row -> Lean evidence). -/
def lemma22StepObligations : List (String × String × String) :=
  [ ("Lemma 2.2 STEP: S' = phi(S), beta' = phi(beta)", "corpus Lemma 2.2 lines 106-135 (apply Lemma 2.1 [C=2] to lambda*S, f+f0)", "CONSTRUCTED: lemma22StepOfData / lemma22StepOfPoly / lemma22Step_exists"),
    ("|S'| < |S| (strict cardinal collapse; main risk)", "Lemma 2.1 polynomial g = x^m(x-1)^n + f0 has g(0)=g(1)=f0", "PROVED: card_image_lt_of_not_injOn / card_image_lt_of_collision / lemma22Step_card_lt"),
    ("Lemma 2.1 (a): phi(S) inside target", "Mzk1Lemma21dAssemblyActual (Lemma 2.1 (a))", "encoded: targetS := image, preserves = image membership"),
    ("Lemma 2.1 (b): unramifiedness away from target", "Mzk1PolyMapActual.polyUnramifiedAt (derivative test PROVED)", "CONSUMED as explicit hypothesis (unramified)"),
    ("Lemma 2.1 (c): phi(beta) outside target", "Lemma 2.1 (c)", "CONSUMED as explicit hypothesis (avoids)"),
    ("lambda*S and f0 normalization", "paper: apply Lemma 2.1 to lambda*S and use f+f0", "encoded by the choice of g (explicit hypothesis; not reconstructed)"),
    ("composition with induction hypothesis", "Mzk1Lemma22CompositionActual.mzk1Lemma22_comp_witness (PROVED)", "CONSUMED: lemma22Step_compose") ]

/-- A71 corpus references for this file (data). -/
def lemma22StepCorpusRefs : List (String × String) :=
  [ ("Lemma 2.1 (a)-(d) proof", "corpus ~lines 35-105 (r = m/(m+n); f0 = -min f)"),
    ("Lemma 2.2 statement + proof", "corpus lines 106-135 (induction on |S|; apply Lemma 2.1 to lambda*S)"),
    ("Lemma 2.2 conditions (i)-(iii)", "0,inf in S; alpha>0; beta/alpha >= 2") ]

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepConstructionActual

end
