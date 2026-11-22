/-
# Mzk1LayerAConsumerActual — Layer A (paper-scope Q̄) conditional consumer wiring

SCOPE (Lead A313/A314; mainline A321): this file records the CONDITIONAL consumer chain
for Layer A of [Mzk1] Lemma 2.4, i.e. the paper-scope target for algebraic (Q̄) inputs.
It does NOT prove the paper-scope target, does NOT reduce the named algebraic nested
induction input, and does NOT claim closure of paper Lemma 2.4.

PROVED here (conditional wiring only):
* `paperScope_of_algebraicNestedInduction` : the named Layer A input implies the
  paper-scope Lemma 2.4 statement;
* `algebraicNestedInduction_iff_paperScope` : the named input is definitionally the
  paper-scope statement (wiring, not a reduction);
* `rationalTarget_of_named` : the named beta-avoiding Belyi base input implies the
  restated F = Q target for every rational state;
* `layerAConsumerStatement_proved` : the Layer A consumer statement;
* `finiteGaloisDescentClaim_proved` : the finite-Galois descent layer (proved in
  Mzk1Lemma24DescentActual, repackaged here as a named claim);
* `mobiusQbar_mapsTo_specialSet_iff` : the Q̄-typed Möbius special-set asset available
  to the named 2.3 layer (repackaged from Mzk1MoebiusP1QbarActual).

NAMED / NOT PROVED: `AlgebraicNestedInductionInput` (class-B; definitionally the
paper-scope target), `AlgebraicClosureFixedFieldPaperInput` (class-B), the 2.3 Möbius
separation application over Q̄/C, and `BetaAvoidingBelyiBaseInput` (class-B, F = Q base).

No `sorry`, no new axiom, no PUnit/True placeholder.
-/
import Mathlib
import tmp.sheaf.xif.paper.LayerAAlgebraicInductionActual
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.RestatedLemma24InductionActual
import tmp.sheaf.xif.paper.Mzk1Lemma24BaseProviderRestatedActual
import tmp.sheaf.xif.paper.Mzk1Lemma24DescentActual
import tmp.sheaf.xif.paper.Mzk1MoebiusP1QbarActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1LayerAConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InductionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseProviderRestatedActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24DescentActual

/-! ### 1. Paper-scope target from the named Layer A induction input -/

/-- **(1) Layer A wiring (PROVED, conditional)**: the named algebraic nested induction
input yields the paper-scope Lemma 2.4 statement for Q̄ inputs. -/
theorem paperScope_of_algebraicNestedInduction
    (h : AlgebraicNestedInductionInput) : PaperScopeLemma24Statement :=
  h

/-- The named Layer A input is definitionally the paper-scope target statement.  Recorded
explicitly so that the conditional wiring above is not mistaken for an independent
reduction or a proof of the paper-scope target. -/
theorem algebraicNestedInduction_iff_paperScope :
    AlgebraicNestedInductionInput ↔ PaperScopeLemma24Statement :=
  Iff.rfl

/-! ### 2. Rational (F = Q) target from the named base input -/

/-- **(2) Rational-input target from the named base (PROVED, conditional)**: the named
beta-avoiding rational Belyi base input yields the restated 2.4 target for every finite
rational point set S and rational beta not in S.  This is the F = Q component only. -/
theorem rationalTarget_of_named
    (h : BetaAvoidingBelyiBaseInput) :
    ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ), β ∉ S → Mzk1Lemma24Target S β :=
  s3135_target_of_betaAvoidingBelyiBase h

/-! ### 3. Layer A ledger: layers, statuses, and exact named inputs -/

/-- The finite-Galois descent statement of Layer A (paper 2.4 lines 159-160), packaged as
a proposition.  It is PROVED (see `finiteGaloisDescentClaim_proved`). -/
def FiniteGaloisDescentClaim : Prop :=
  ∀ {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (x : E), (∀ σ : E ≃ₐ[F] E, σ x = x) → ∃ f : F, algebraMap F E f = x

/-- The finite-Galois descent layer is PROVED (Mzk1Lemma24DescentActual). -/
theorem finiteGaloisDescentClaim_proved : FiniteGaloisDescentClaim := by
  intro F E _ _ _ _ _ x hx
  exact s3135_descent_finite_galois x hx

/-- Proved Q̄-typed Möbius asset available to the named 2.3 layer: the special-set maps-to
criterion for Möbius transformations over Q̄.  The 2.3 application/separation step itself
remains named (see `mobius23Row`). -/
theorem mobiusQbar_mapsTo_specialSet_iff
    (M : LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1QbarActual.MoebiusDataAC) :
    Set.MapsTo M.mapPoints
        LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1QbarActual.specialSet
        LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1QbarActual.specialSet ↔
      M.mapPoints (P1Point.ofFinite (0 : AlgebraicClosure ℚ)) ∈
          LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1QbarActual.specialSet ∧
        M.mapPoints (P1Point.ofFinite (1 : AlgebraicClosure ℚ)) ∈
          LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1QbarActual.specialSet ∧
        M.mapPoints P1Point.infty ∈
          LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1QbarActual.specialSet :=
  LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1QbarActual.mapsTo_specialSet_iff M

/-- One row of the Layer A ledger.  `status` uses the audit vocabulary; `gap` is the
exact remaining obligation (empty exactly for proved rows). -/
structure LayerARow where
  id : String
  layer : String
  status : Audit.VerificationStatus
  formalRef : String
  gap : String
  deriving Repr

/-- Layer A row (D): finite-Galois descent — PROVED. -/
def descentRow : LayerARow :=
  { id := "MZK1.lemma24.layerA.descent"
    layer := "(D) finite-Galois descent (paper Lemma 2.4 lines 159-160)"
    status := Audit.VerificationStatus.proved
    formalRef :=
      "Mzk1Lemma24DescentActual.s3135_descent_finite_galois; s3135_coeff_descent_finite_galois"
    gap := "" }

/-- Layer A row (D): infinite fixed field over Q̄ — class-B named. -/
def fixedFieldRow : LayerARow :=
  { id := "MZK1.lemma24.layerA.fixed-field"
    layer := "(D) infinite fixed field over Q̄"
    status := Audit.VerificationStatus.interface
    formalRef := "Mzk1Lemma24DescentActual.AlgebraicClosureFixedFieldPaperInput"
    gap :=
      "class-B named: infinite Galois fixed-field theorem over Q̄; only the finite-dimensional Mathlib fixed-field API is available (conditional s3135_coeff_descent_algebraicClosure_of_paperInput)" }

/-- Layer A row 2.3: Möbius separation over Q̄/C — named layer. -/
def mobius23Row : LayerARow :=
  { id := "MZK1.lemma24.layerA.mobius-2.3"
    layer := "2.3 Möbius separation over Q̄/C"
    status := Audit.VerificationStatus.interface
    formalRef :=
      "Mzk1MoebiusP1QbarActual (MoebiusDataAC, mapsTo_specialSet_iff, moebiusCriticalValues_eq_empty); Mzk1MoebiusP1CActual (C-typed); Mzk1MoebiusP1Actual (Q-typed)"
    gap :=
      "named layer: Q̄/C-typed Möbius library assets are proved, but the paper 2.3 application/separation step at paper scope is not wired" }

/-- Layer A row: algebraic nested (m,d) induction — class-B named. -/
def algebraicInductionRow : LayerARow :=
  { id := "MZK1.lemma24.layerA.algebraic-nested-induction"
    layer := "algebraic nested (m,d) induction (paper Lemma 2.4 lines 163-206)"
    status := Audit.VerificationStatus.interface
    formalRef :=
      "PaperScopeLemma24Actual.AlgebraicNestedInductionInput = PaperScopeLemma24Statement; LayerAAlgebraicInductionActual.AlgebraicNestedInductionStatement"
    gap :=
      "class-B named: the named input is definitionally the paper-scope target; no independent proof" }

/-- The exact named input of the rational (F = Q) component: the beta-avoiding Belyi base. -/
def betaAvoidingBaseRow : LayerARow :=
  { id := "MZK1.lemma24.rational.base"
    layer := "F = Q component base: beta-avoiding rational Belyi map"
    status := Audit.VerificationStatus.interface
    formalRef :=
      "RestatedLemma24InductionActual.BetaAvoidingBelyiBaseInput; Mzk1Lemma24BaseProviderRestatedActual.s3135_target_of_betaAvoidingBelyiBase"
    gap :=
      "class-B named: TauCeti Belyification controls q(S) and the critical values but not q(beta); the conditional theorem consumes the input" }

/-- Full Layer A ledger: descent (PROVED) plus the three named layers. -/
def layerARows : List LayerARow :=
  [descentRow, fixedFieldRow, mobius23Row, algebraicInductionRow]

/-- Exactly the NAMED (unproved) layers of the paper-scope Layer A reduction.  The
finite-Galois descent row is omitted because it is PROVED. -/
def layerANamedRows : List LayerARow :=
  [fixedFieldRow, mobius23Row, algebraicInductionRow]

/-- Exact named input consumed by the F = Q component theorem. -/
def rationalNamedRows : List LayerARow :=
  [betaAvoidingBaseRow]

theorem layerARows_length : layerARows.length = 4 := rfl

theorem layerANamedRows_length : layerANamedRows.length = 3 := rfl

theorem rationalNamedRows_length : rationalNamedRows.length = 1 := rfl

/-! ### 4. Layer A consumer statement and record -/

/-- **Layer A consumer target**: the paper-scope [Mzk1] Lemma 2.4 statement for Q̄ inputs
(S finite in P¹(Q̄), beta in Q̄ minus S). -/
abbrev LayerAConsumerTarget : Prop := PaperScopeLemma24Statement

/-- Bridge to the Layer A status module: its named algebraic-induction statement alias is
the same paper-scope target as this consumer's target. -/
theorem layerAStatementAlias_iff_consumerTarget :
    LeanFormal.IUT.XiFPaper.LayerAAlgebraicInductionActual.AlgebraicNestedInductionStatement ↔
      LayerAConsumerTarget :=
  Iff.rfl

/-- **Layer A consumer statement (CONDITIONAL)**: the named algebraic nested induction
input yields the paper-scope target.  The named input is unproved (and definitionally the
target), so this is not a closure of paper Lemma 2.4. -/
def LayerAConsumerStatement : Prop :=
  AlgebraicNestedInductionInput → LayerAConsumerTarget

/-- The Layer A consumer statement is PROVED from the named input (conditional wiring;
no closure claim). -/
theorem layerAConsumerStatement_proved : LayerAConsumerStatement :=
  paperScope_of_algebraicNestedInduction

/-- **Layer A consumer record** (audit): paper-scope target for Q̄ inputs together with the
exact named layers.  Status `interface`: CONDITIONAL, not proved, no closure. -/
def LayerAConsumerRecord : Audit.Obligation :=
  { id := "MZK1.lemma24.layerA.consumer"
    source :=
      "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 144-206; Lead A313/A314 scope split"
    status := Audit.VerificationStatus.interface
    note :=
      "LAYER A CONSUMER (paper-scope Qbar inputs; CONDITIONAL, no closure): paperScope_of_algebraicNestedInduction : AlgebraicNestedInductionInput -> PaperScopeLemma24Statement; rationalTarget_of_named : BetaAvoidingBelyiBaseInput -> forall S beta, beta notin S -> Mzk1Lemma24Target S beta (F = Q component); LayerAConsumerStatement (definitionally AlgebraicNestedInductionInput -> PaperScopeLemma24Statement) PROVED by conditional wiring. Layers: (D) finite-Galois descent PROVED (s3135_descent_finite_galois / s3135_coeff_descent_finite_galois); (D) infinite fixed field class-B named (AlgebraicClosureFixedFieldPaperInput); 2.3 Moebius over Qbar/C named (Qbar/C Moebius library assets proved: MoebiusDataAC, mapsTo_specialSet_iff, moebiusCriticalValues_eq_empty; application/separation step not wired); AlgebraicNestedInductionInput class-B named (paper 163-206 nested (m,d) induction; definitionally PaperScopeLemma24Statement). NOT paper-complete; NOT a reduction of the named input; gate NOT PASSED; binding HOLD; registry frozen 14041. Coverage statement verbatim: F=Q component delivered + full-Qbar reduction named (not complete)."
    dependsOn :=
      [ "MZK1.lemma24.paper-scope", "MZK1.lemma24.descent", "MZK1.lemma24.base-provider-restated",
        "MZK1.lemma24.rational-input-scope" ]
    sorryItems :=
      [ "AlgebraicNestedInductionInput (class-B named; definitionally PaperScopeLemma24Statement)",
        "AlgebraicClosureFixedFieldPaperInput (class-B named; infinite Galois fixed field over Qbar)",
        "2.3 Moebius separation over Qbar/C (named layer; application step not wired)",
        "BetaAvoidingBelyiBaseInput (class-B named; F = Q component base)" ] }

#check paperScope_of_algebraicNestedInduction
#check rationalTarget_of_named
#check layerAConsumerStatement_proved
#check layerAStatementAlias_iff_consumerTarget
#check LayerAConsumerRecord
#check mobiusQbar_mapsTo_specialSet_iff

end LeanFormal.IUT.XiFPaper.Mzk1LayerAConsumerActual
end
