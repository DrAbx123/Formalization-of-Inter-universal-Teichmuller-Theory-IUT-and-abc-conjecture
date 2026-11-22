import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.APT
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SHE

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Actual IPL links and APT transport evidence

This file builds the actual IPL link-isomorphism surface and the APT
transport/evidence surface from the source Kummer/evaluation/link data of
SourceKummerEvaluationArrows.lean, and ties the evidence to the reduced
SourceAlgorithmicParallelTransport record of APT.lean.

## Actual content

* IPLActual: the frozen IPL composite of Remark 3.11.1, (iii), with its actual
  FPrimeStripEquiv components, Kummer arrow, evaluation arrow, and the
  factorization law. This is the actual single-representative form: the full
  poly-isomorphism and the x-mu layer are not silently replaced.
* KummerEvaluationActual: the actual Kummer-evaluation square of Remark
  3.10.2, with its two-path equality.
* APTActualEvidence: carries actual IPL data, the Kummer-evaluation square,
  and an actual SourceAlgorithmicParallelTransport when the algorithm
  instances and SHE landing data are available. The evidence proposition is a
  real conjunction of source factorization/two-path statements, not True.

## Exact gaps (not uninterpreted, not toy)

1. The source algorithms and their (Ind1)/(Ind2) actions over the actual
   output carriers are not constructed here; the transport field is an input.
2. The full F^boxplus-triangleright-x-mu prime-strip and x-mu layer are not
   represented; FPrimeStripEquiv is a single representative (API-1 gap).
3. The log-Kummer/(Ind3) upper-semi content and the actual SHE landing datum
   remain named source cards of APT.lean/SourceArithmeticHolomorphicLanding.
4. Adjacent-column procession isomorphisms and the vertical shift adjustment
   are not constructed here.
-/

noncomputable section

namespace LeanFormal.IUT
namespace Theorem311Source

universe uG uv ua upi umon ui uOut1 uOut2

variable {V : Type uv}
variable {G : Type uG} [Group G] [TopologicalSpace G]

/-! ## 1. Actual IPL link isomorphisms -/

/-- The actual IPL composite data of IUT III, Remark 3.11.1, (iii), in reduced
source form: two lower horizontals, the first vertical Kummer arrow, the
collapsed evaluation arrow, the linking isomorphism, and the frozen
factorization. The fields are actual FPrimeStripEquiv / SourceKummerArrow /
SourceEvaluationArrow objects. No inhabitant is asserted. -/
structure IPLActual
    (intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V) where
  lowerHorizontal1 : FPrimeStripEquiv gauStrip intermediateStrip
  lowerHorizontal2 : FPrimeStripEquiv envStrip gauStrip
  kummer : SourceKummerArrow G envStrip coricEnvStrip
  evaluation : SourceEvaluationArrow G coricEnvStrip qPilotStrip
  inputLink : FPrimeStripEquiv intermediateStrip qPilotStrip
  factorization :
    inputLink =
      (lowerHorizontal1.symm).trans
        ((lowerHorizontal2.symm).trans
          (kummer.stripIso.trans evaluation.stripIso))

namespace IPLActual

variable {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip :
  FPrimeStrip V}

/-- The named IPL composite on the right-hand side of the frozen formula. -/
def composite (L : IPLActual (G := G) intermediateStrip gauStrip envStrip
    coricEnvStrip qPilotStrip) : FPrimeStripEquiv intermediateStrip qPilotStrip :=
  (L.lowerHorizontal1.symm).trans
    ((L.lowerHorizontal2.symm).trans
      (L.kummer.stripIso.trans L.evaluation.stripIso))

/-- The actual IPL factorization: the linking isomorphism is the composite of
the Kummer/evaluation arrows. -/
theorem inputLink_eq_composite
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip) :
    L.inputLink = L.composite :=
  L.factorization

/-- Packaging as the frozen SourceLinkFactorization record. -/
def toLinkFactorization (L : IPLActual (G := G) intermediateStrip gauStrip
    envStrip coricEnvStrip qPilotStrip) :
    SourceLinkFactorization G intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip where
  lowerHorizontal₁ := L.lowerHorizontal1
  lowerHorizontal₂ := L.lowerHorizontal2
  kummer := L.kummer
  evaluation := L.evaluation
  inputLink := L.inputLink
  factorization := L.factorization

@[simp] theorem toLinkFactorization_inputLink
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip) :
    (L.toLinkFactorization).inputLink = L.inputLink := rfl

/-- The factorization law restated for the packaged record. -/
theorem toLinkFactorization_factorization
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip) :
    (L.toLinkFactorization).inputLink =
      (L.toLinkFactorization).composite :=
  L.toLinkFactorization.inputLink_eq_composite

/-- The inverse IPL link is an actual strip equivalence. -/
def inverse (L : IPLActual (G := G) intermediateStrip gauStrip envStrip
    coricEnvStrip qPilotStrip) : FPrimeStripEquiv qPilotStrip intermediateStrip :=
  L.inputLink.symm

@[simp] theorem inverse_inputLink
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip) :
    L.inverse = L.inputLink.symm := rfl

/-- The actual IPL link is compatible with its Kummer/evaluation factors. -/
theorem ipl_compatibility
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip) :
    L.inputLink =
      (L.lowerHorizontal1.symm).trans
        ((L.lowerHorizontal2.symm).trans
          (L.kummer.stripIso.trans L.evaluation.stripIso)) :=
  L.factorization

end IPLActual

/-! ## 2. Actual Kummer-evaluation square -/

/-- The source Kummer-evaluation square of Remark 3.10.2 together with its
proved two-path equality. This is an actual record; no inhabitant is asserted. -/
structure KummerEvaluationActual
    (upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V) where
  square : SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft lowerRight

namespace KummerEvaluationActual

variable {upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V}

@[simp] theorem square_domainExpression
    (K : KummerEvaluationActual (G := G) upperLeft upperRight lowerLeft lowerRight) :
    K.square.domainExpression =
      (K.square.leftKummer.stripIso.symm).trans K.square.lowerHorizontal.stripIso :=
  rfl

@[simp] theorem square_codomainExpression
    (K : KummerEvaluationActual (G := G) upperLeft upperRight lowerLeft lowerRight) :
    K.square.codomainExpression =
      (K.square.upperHorizontal.stripIso).trans
        (K.square.rightKummer.stripIso.symm) :=
  rfl

/-- The actual Kummer-evaluation two-path equality. -/
theorem domainExpression_eq_codomainExpression
    (K : KummerEvaluationActual (G := G) upperLeft upperRight lowerLeft lowerRight) :
    K.square.domainExpression = K.square.codomainExpression :=
  K.square.domainExpression_eq_codomainExpression

end KummerEvaluationActual

/-! ## 3. APT transport/evidence -/

variable {l : PrimeGeFive}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n n' : Int}
variable {G1 : Type uG} [Group G1] {G1' : Type uG} [Group G1']
variable {G2 : Type uG} [Group G2]
variable {Output1 : Type uOut1} {Output2 : Type uOut2}
variable {S : SourceOneColumnArithmeticHolomorphicStructure V}
variable {A : SourceTheorem311MultiradialAlgorithm G1 G2 I n Output1}
variable {A' : SourceTheorem311MultiradialAlgorithm G1' G2 I n' Output2}

/-- Actual APT evidence: IPL link data, the Kummer-evaluation square, and the
reduced algorithmic parallel transport. The transport is an input; the actual
algorithm instances and SHE landing are separate source obligations. -/
structure APTActualEvidence
    (intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V)
    (upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V) where
  ipl : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip
    qPilotStrip
  kummerEvaluation : KummerEvaluationActual (G := G) upperLeft upperRight
    lowerLeft lowerRight
  transport : SourceAlgorithmicParallelTransport S A A'

namespace APTActualEvidence

variable {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip :
  FPrimeStrip V}
variable {upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V}

/-- The actual IPL link exposed by APT evidence. -/
def iplLink
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    FPrimeStripEquiv intermediateStrip qPilotStrip :=
  E.ipl.inputLink

/-- The actual transport record carried by APT evidence. -/
def toTransport
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    SourceAlgorithmicParallelTransport S A A' :=
  E.transport

/-- The APT statement of the reduced interface follows from the transported
record. -/
theorem aptStatement
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    SourceAPTStatement S A A' :=
  ⟨E.transport⟩

/-- The actual evidence proposition carried by APT: the IPL factorization and
the Kummer-evaluation two-path equality hold simultaneously. It is a real
conjunction of source compatibilities. -/
def evidenceProp
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) : Prop :=
  E.ipl.inputLink = E.ipl.composite ∧
    E.kummerEvaluation.square.domainExpression =
      E.kummerEvaluation.square.codomainExpression

/-- The actual APT evidence proposition is proved from the source
factorization and two-path laws. -/
theorem evidenceProp_holds
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    E.evidenceProp :=
  ⟨E.ipl.inputLink_eq_composite,
    E.kummerEvaluation.domainExpression_eq_codomainExpression⟩

/-- Transfer of APT evidence into a north-wall APT slot assembly. -/
theorem aptSlot_evidence
    (X : SourceAPTSlotAssembly S A A')
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    X.contract.apt :=
  X.aptSlot_evidence E.aptStatement

end APTActualEvidence

/-! ## 4. Exact residual source obligations -/

/-- The actual algorithm instances over the source output carriers are not
constructed by this file; this is a named proposition, not an uninterpreted declaration. -/
def AlgorithmInstancesRequired : Prop :=
  Nonempty (SourceTheorem311MultiradialAlgorithm G1 G2 I n Output1) ∧
    Nonempty (SourceTheorem311MultiradialAlgorithm G1' G2 I n' Output2)

/-- The SHE landing datum required by the reduced APT record, as an exact
named source condition. -/
def SHELandingRequired : Prop :=
  SourceLocalizationExpressible S Output2

/-- Exact status: the IPL factorization and Kummer-evaluation compatibility
are proved from actual source data; the APT transport and SHE landing are
explicit inputs/obligations, not consequences. -/
theorem ipl_compatibility_status
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip) :
    L.inputLink = L.composite :=
  L.inputLink_eq_composite

end Theorem311Source
end LeanFormal.IUT

end
