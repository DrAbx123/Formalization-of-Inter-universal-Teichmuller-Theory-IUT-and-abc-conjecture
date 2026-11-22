import tmp.sheaf.xif.paper.Mzk1Thm25P1CompositeConsumerDesignActual
import tmp.sheaf.xif.paper.Mzk1Thm25P1CompositeConsumerActual
import tmp.sheaf.xif.paper.Mzk1GeometricCorePreciseActual
import tmp.sheaf.xif.paper.Mzk1GeomCorePreciseToOldActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1P1ConsumerDeepInputsActual — Problem D/E named inputs in the consumer design

STEP 0 prior-art (reuse, no re-proof):
* stepxi Mzk1Thm25P1CompositeConsumerDesignActual: P1CompositeConsumerInputs /
  P1CompositeConsumerStatement / P1CompositeRealConsumerTarget / CPointCriticalValuesIn01;
* stepxi Mzk1Thm25P1CompositeConsumerActual (CITABLE 12): p1CompositeRealConsumerTarget_rational
  (P1CompositeRealConsumerTarget PROVED at F=Q scope) and the 2.2 o 2.3 composition;
* stage4 Mzk1GeometricCorePreciseActual: MapsTToZero / UnramifiedOverZero /
  PullbackIsoDegree / Mzk1GeometricCoreWitnessPrecise / Mzk1GeometricCoreRecastPrecise
  (Problem D precise geometric schema);
* Mzk1GeomCorePreciseToOldActual: toOldWitness / toOldRecast (precise -> old conversion PROVED).

DELIVERED HERE (new file, no green file modified): the Problem D / Problem E named inputs are
added as EXPLICIT PARAMETERS of an extended consumer input bundle, and a CONDITIONAL
P1CompositeConsumer statement is proved from the already-proved F=Q target (antecedents are
NOT asserted true).  Records state which inputs the F=Q chain has CONSUMED and which remain
NAMED.  Scope: F=Q component only; full P1(Qbar) reduction named; NO closure claim; gate NOT
PASSED; h22 binding HOLD.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1P1ConsumerDeepInputsActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCorePreciseToOldActual

universe u

/-- **Problem D named inputs** (H6 GeometricCore): the precise witness exists
(Mzk1GeometricCoreRecastPrecise; named class-B paper input) and the full line-bundle
isomorphism psi^* O(1) ~= O(D) (named deep input: no line-bundle/divisor API in pinned
Mathlib; only the degree identity PullbackIsoDegree is formalized). -/
structure ProblemDDeepInputs {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) where
  precise_witness_exists : Mzk1GeometricCoreRecastPrecise c ε T D
  line_bundle_iso : Prop

/-- **Problem E named inputs** (deep IUT rows; out of formalization scope, recorded as
explicit placeholders so the consumer bundle is honest about what is still missing). -/
structure ProblemEDeepInputs where
  absTopIII05 : Prop
  h5_Ox_stabilization : Prop
  h7_ob9_arbitrary_iterate : Prop
  etth_realization_deeper : Prop
  iutIV_uniform_height_volume : Prop

/-- Extended consumer input bundle: the existing P1CompositeConsumerInputs plus the
Problem D / Problem E named inputs as explicit fields. -/
structure P1CompositeConsumerInputsDeep {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) where
  base : P1CompositeConsumerInputs
  problemD : ProblemDDeepInputs c ε T D
  problemE : ProblemEDeepInputs

/-- Build the extended bundle from a base bundle and the named Problem D/E inputs. -/
def mkDeepInputs {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (base : P1CompositeConsumerInputs)
    (hD : Mzk1GeometricCoreRecastPrecise c ε T D) (hIso : Prop)
    (hE : ProblemEDeepInputs) : P1CompositeConsumerInputsDeep c ε T D :=
  { base := base
    problemD := { precise_witness_exists := hD, line_bundle_iso := hIso }
    problemE := hE }

/-- **Conditional statement (Problem D):** assuming the Problem D precise witness exists,
the real P1 composite consumer target holds. -/
def P1CompositeConsumerStatementDeep {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (I : P1CompositeConsumerInputsDeep c ε T D) : Prop :=
  Mzk1GeometricCoreRecastPrecise c ε T D → P1CompositeRealConsumerTarget

/-- **Conditional statement (Problem D + Problem E placeholders):** both named deep input
groups are antecedents; the consequent is the F=Q real consumer target. -/
def P1CompositeConsumerDeepStatement {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (I : P1CompositeConsumerInputsDeep c ε T D) : Prop :=
  (Mzk1GeometricCoreRecastPrecise c ε T D → P1CompositeRealConsumerTarget) ∧
  (I.problemE.absTopIII05 → P1CompositeRealConsumerTarget)

/-- The conditional Problem D statement follows from the PROVED F=Q consumer target
(the Problem D witness is an antecedent, NOT asserted true). -/
theorem p1CompositeConsumerStatementDeep_of_FQ {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (I : P1CompositeConsumerInputsDeep c ε T D) :
    P1CompositeConsumerStatementDeep I :=
  fun _ => p1CompositeRealConsumerTarget_rational

/-- The conditional Problem D + Problem E statement follows from the PROVED F=Q consumer
target (all deep inputs are antecedents, NOT asserted true). -/
theorem p1CompositeConsumerDeepStatement_of_FQ {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (I : P1CompositeConsumerInputsDeep c ε T D) :
    P1CompositeConsumerDeepStatement I :=
  ⟨fun _ => p1CompositeRealConsumerTarget_rational,
   fun _ => p1CompositeRealConsumerTarget_rational⟩

/-- The base statement of the bundle's base inputs is the design consumer statement; it is
the F=Q real consumer target (PROVED). -/
theorem baseStatement_of_FQ {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (I : P1CompositeConsumerInputsDeep c ε T D) :
    P1CompositeConsumerStatement I.base :=
  p1CompositeRealConsumerTarget_rational

/-- Input/record rows: which inputs the F=Q chain has CONSUMED and which remain NAMED. -/
def p1ConsumerDeepInputRows : List (String × String × String) :=
  [ ("F=Q CONSUMED: rational 2.2 gate", "stage4 Mzk1Lemma22RationalGateActual.mzk1Lemma22_target_rational", "CONSUMED (PROVED)"),
    ("F=Q CONSUMED: 2.3 Moebius layer", "qpilot Mzk1MoebiusP1Actual/Mzk1MoebiusP1CActual (MoebiusData, specialSetQ, CV empty)", "CONSUMED (CITABLE)"),
    ("F=Q CONSUMED: 2.4 conditional base", "abc Mzk1Consumer24AdapterActual.h24BaseConcrete (BetaAvoidingBelyiBaseInput named class-B)", "CONSUMED CONDITIONALLY"),
    ("F=Q CONSUMED: CV composition law", "RestatedLemma24CVLawActual / RestatedLemma24InterfaceActual.CVCompositionLawStatement", "CONSUMED (PROVED)"),
    ("F=Q CONSUMED: C-point CV control", "Mzk1Thm25P1CompositeConsumerActual.p1CompositeRealConsumerTarget_rational", "CONSUMED (PROVED)"),
    ("NAMED: full 2.2 gate slot h22", "P1CompositeConsumerInputs.h22 (Lemma22FullStatementShape)", "NAMED PARAMETER (binding HOLD)"),
    ("NAMED: Problem D precise witness", "ProblemDDeepInputs.precise_witness_exists : Mzk1GeometricCoreRecastPrecise c ε T D (toOld conversion PROVED in Mzk1GeomCorePreciseToOldActual)", "NAMED class-B"),
    ("NAMED: Problem D line-bundle isomorphism", "ProblemDDeepInputs.line_bundle_iso : psi^* O(1) ~= O(D) (no line-bundle/divisor API)", "NAMED deep placeholder"),
    ("NAMED: Problem E deep IUT inputs", "ProblemEDeepInputs (AbsTopIII05, H5 O^x stabilization, H7/Ob9 iterate, EtTh deeper, IUT IV height-volume)", "NAMED deep placeholders (out of scope)"),
    ("NAMED: full P1(Qbar) reduction", "AlgebraicNestedInductionInput (paper 179-206 m/d step) + descent layers", "NAMED (paper-scope)"),
    ("scope/status", "F=Q component only; full P1(Qbar) reduction NAMED; NO closure; gate NOT PASSED; h22 binding HOLD", "INTEGRITY") ]

theorem p1ConsumerDeepInputRows_length : p1ConsumerDeepInputRows.length = 11 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1ConsumerDeepInputsActual

end
