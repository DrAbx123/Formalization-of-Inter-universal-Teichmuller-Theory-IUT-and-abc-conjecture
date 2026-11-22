import Mathlib
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma24Proof2Actual
import tmp.sheaf.xif.paper.Mzk1Lemma24MeasureActual
import tmp.sheaf.xif.paper.Mzk1Lemma24BaseCaseActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24AssemblyActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24Proof2Actual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24ProofActual

/-- The [Mzk1] Lemma 2.4 obligation at the stage4 P^1-morphism interface level: there
is a P^1-morphism preserving S into some target set, avoiding beta, and unramified
away from the target (with the unramifiedness datum supplied as part of the
conclusion). -/
def Mzk1Lemma24Goal (S : Finset (P1Point ℂ)) (β : P1Point ℂ) : Prop :=
  ∃ (targetSet : Set (P1Point ℂ)) (unramifiedAt : P1Point ℂ → Prop),
    Mzk1Lemma24StatementShape ℂ S β targetSet unramifiedAt

/-- State of the nested induction: the current finite set and base point. -/
abbrev Mzk1State : Type := Finset (P1Point ℂ) × P1Point ℂ

/-- A single induction step: the next state, the measure decrease, and the transport of
the goal at the next state to the current one (composition of P^1-morphisms via the
stage4 interface / hull's transfer lemmas). -/
structure Mzk1Lemma24Step (μ : Mzk1State → Nat × Nat) (st : Mzk1State) where
  next : Mzk1State
  decrease : lemma24Measure (μ next) (μ st)
  transport : Mzk1Lemma24Goal next.1 next.2 → Mzk1Lemma24Goal st.1 st.2

/-- **Nested (m,d)-induction assembly skeleton** (paper [Mzk1] Lemma 2.4 lines
179-206): given a measure function mu on states with well-founded lexicographic value,
a base provider at measure (0,0), and a step provider off (0,0) with measure decrease
and goal transport, the Lemma 2.4 goal holds for every state. -/
theorem mzk1Lemma24_assembly
    (μ : Mzk1State → Nat × Nat)
    (hwf : WellFounded (fun a b : Mzk1State => lemma24Measure (μ a) (μ b)))
    (base : ∀ st : Mzk1State, μ st = (0, 0) → Mzk1Lemma24Goal st.1 st.2)
    (step : ∀ st : Mzk1State, μ st ≠ (0, 0) → Mzk1Lemma24Step μ st) :
    ∀ st : Mzk1State, Mzk1Lemma24Goal st.1 st.2 := by
  intro st
  let r : Mzk1State → Mzk1State → Prop := fun a b => lemma24Measure (μ a) (μ b)
  have hmain : ∀ x : Mzk1State, Mzk1Lemma24Goal x.1 x.2 := by
    refine hwf.fix ?_
    intro x rec
    by_cases hx : μ x = (0, 0)
    · exact base x hx
    · exact (step x hx).transport (rec (step x hx).next (step x hx).decrease)
  exact hmain st

/-- Named residue for paper-obligation closure: the step provider for nonzero measure.
Its construction is exactly the f0-measure-decrease bookkeeping of the paper (lines
195-203: for alpha' in f0(S0) one has [Q(alpha'):Q] < d0, hence m(S'),d(S') decrease),
and the transport is the composition of the f0 P^1-morphism (ShapeStep) with the
normalization/affine transfer. -/
def Mzk1Lemma24StepProviderStatement : Prop :=
  ∀ (μ : Mzk1State → Nat × Nat), (∀ st : Mzk1State, μ st ≠ (0, 0) →
    Nonempty (Mzk1Lemma24Step μ st))

/-- Named residue: the base provider at measure (0,0) (rational case).  Our rational
base case s3135_base_case_shape proves the corresponding construction over Q; lifting it
to ℂ (with rational points embedded) is the remaining wiring. -/
def Mzk1Lemma24BaseProviderStatement : Prop :=
  ∀ (μ : Mzk1State → Nat × Nat), ∀ st : Mzk1State,
    μ st = (0, 0) → Mzk1Lemma24Goal st.1 st.2

/-- Assembly status: the well-founded nested-induction skeleton is PROVED; the two
providers are the exact remaining named residues (f0-measure-decrease bookkeeping and
rational base lifting), with all component evidence (G/F/D/M, normalization, transfer)
in place. -/
def s3135Mzk1AssemblyStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.assembly"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 144-206"
    status := Audit.VerificationStatus.interface
    note := "PROVED: mzk1Lemma24_assembly (well-founded recursion over the lexicographic measure lemma24Measure with base/step providers and goal transport). Consumes Mzk1Lemma24Proof2Actual (lemma24Measure + strong induction principle), Mzk1Lemma24MeasureActual (m/d monotonicity/closure results), stage4 P1MorphismInterface, and (in provider instantiations) Mzk1Lemma24ShapeStepActual/StatementShapeActual, Mzk1Lemma23NormalizationActual + Mzk1Lemma24NormalizationTransferActual (L2.3), Mzk1Lemma24F0BoundActual/Growth/BetaAvoidance/Descent/Union. REMAINING named residues: Mzk1Lemma24StepProviderStatement (f0-measure-decrease bookkeeping paper lines 195-203 + transport composition) and base provider (rational case lift from Q to C). No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.measure-monotonicity", "MZK1.lemma24.statement-shape" ]
    sorryItems :=
      [ "Mzk1Lemma24StepProviderStatement (f0-measure-decrease bookkeeping lines 195-203)",
        "Mzk1Lemma24BaseProviderStatement (rational base case lifted to C)" ] }

#check mzk1Lemma24_assembly
#check Mzk1Lemma24StepProviderStatement
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24AssemblyActual
end