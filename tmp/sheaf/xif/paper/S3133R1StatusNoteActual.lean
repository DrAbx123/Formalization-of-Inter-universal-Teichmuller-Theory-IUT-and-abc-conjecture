import tmp.sheaf.xif.paper.S3133M1InjectionReductionActual
import tmp.sheaf.xif.paper.S3133M2aNormReductionActual
import tmp.sheaf.xif.paper.S3133M2bClauseBDescentActual
import tmp.sheaf.xif.paper.S3133GaussianCompletionTransportActual
import tmp.sheaf.xif.paper.S3133GaussianM2MissingActual

/-!
# R1 status note: minimal residual registry anchors (component, citable status doc)

COMPONENT/documentation module, not a paper object.  Named consumers: lattice
S3137 registry (INDEX.R1.*), mainline M-list/registry, stage4/stepxi.

R1 minimal residual (current, after tasks 28/45/51/57/60/63/66):

  R1 = M1 + M2a + M2b

* M1 (contract-separated): S3133R1M1Node = S3133M1Remaining,
  i.e. Nonempty { e : Bad (nativePlaceSelection T) ~= C3.tensorIndex // forall b,
  placeTransport (nativeBadToFPlace T b) = tensorPlaces (e b) (tensorTuple (e b))
  }.  The bad->all-place INJECTION itself is constructible
  (S3133BadToAllPlaceIndexInjection_of_bijections, PROVED); the genuine missing
  datum is the source placeToMod provenance that the frozen OriginalInput does
  not expose.  REFS: IUT I, Definition 3.1, (b), (e); IUT III, Theorem 3.11,
  pp. 160-162; IUT IV, Theorem 1.10 proof, pp. 26-27.

* M2a (refined node): S3133R1M2aNode = S3133RationalFiveCompletionNorm, i.e. the
  existence of a nonzero element of the rational completion at the five place
  with canonical norm 5^-1.  The Gaussian-completion consequence is PROVED:
  S3133GaussianCanonicalQNorm_of_rationalCompletionNorm
  (S3133M2aNormReductionActual); the actual transport into the Gaussian
  completion and its normalized-norm preservation are PROVED
  (S3133GaussianCompletionTransportActual:
  S3133GaussianPadicCompletionHom,
  S3133GaussianNormalizedTransport_norm_preserving); the rational-side value
  theorem is S3133RationalFiveQ_norm (S3133GaussianBaseQActual).  M2a CLOSURE IS
  PARKED awaiting the two WithVal/WithZero presentation glue steps in
  S3133M2aClosedActual (handoff to lattice task-67).  REFS: IUT I, Example 3.2,
  (iv); IUT III, Definition 3.8, (i), p. 112-113.

* M2b: S3133R1M2bNode = S3133GaussianClauseBDescent, i.e. the clause-B/Tate-q
  descent: at every bad place above 5 the clause-B q has canonical norm 1/5.
  The clause-B q is the actual qVFamily at the lifted F-place (PROVED,
  S3133M2_clauseB_q_parameter); the generic SourceClauseB supplies only an
  arbitrary FinitePlaceQCandidate witness and a Tate curve comparison, so the
  value 1/5 is the paper's chosen q_v (D4).  Linkage with the shrunk model match
  PROVED (S3133M2bClauseBDescentActual).  REFS: IUT I, Definition 3.1, (b), (c);
  IUT I, Example 3.2, (iv); IUT II, Remark 2.5.1, (i); IUT III, Definition 3.8,
  (i).

ACTIVATION STEPS once lattice closes M2a (S3133RationalFiveCompletionNorm):
1. Compile S3133M2aClosedActual with the two presentation glue fixes documented
   in its docstring (WithVal-vs-Coe valued_coe bridge; WithZero.unzero rewrite
   via coe_unzero/exp_eq_coe_ofAdd/coe_injective).  It then provides
   S3133GaussianCanonicalQNorm_holds.
2. Re-activate S3133GaussianModelMapResidualFinalActual (design parked there):
   structure S3133GaussianModelMapResidualFinal with only (C, arithmetic_eq,
   m1_indexInjection, m2b_clauseB, m2b_clauseB_eq), M0/M3 proved,
   S3137R1_interface_final, conversion of_minimal, and
   S3133GaussianQParameterMatchAtBase_iff_clauseB.
3. Message lattice to mark INDEX.R1.M2.base-q-transport CLOSED and R1 = M1 + M2b;
   message mainline registry; append ledger.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133R1StatusNoteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3133M1InjectionReductionActual
open LeanFormal.IUT.XiFPaper.S3133M2aNormReductionActual
open LeanFormal.IUT.XiFPaper.S3133M2bClauseBDescentActual
open LeanFormal.IUT.XiFPaper.S3133GaussianM2MissingActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- Registry anchor M1: the contract-separated placeToMod residual. -/
abbrev S3133R1M1Node
    (T : SourceNativeInitialThetaData.{0} l)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod) : Prop :=
  S3133M1Remaining T C3 placeTransport

/-- Registry anchor M2a: the refined base-completion norm residual. -/
abbrev S3133R1M2aNode : Prop := S3133RationalFiveCompletionNorm

/-- Registry anchor M2b: the clause-B/Tate-q descent residual. -/
abbrev S3133R1M2bNode (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  S3133GaussianClauseBDescent T

/-- Provenance link for the M2a anchor: the refined base-completion norm
residual implies the actual canonical Gaussian q norm condition. -/
theorem S3133R1M2aNode_imp_canonicalQ (h : S3133R1M2aNode) :
    S3133GaussianCanonicalQNorm :=
  S3133GaussianCanonicalQNorm_of_rationalCompletionNorm h

end LeanFormal.IUT.XiFPaper.S3133R1StatusNoteActual
