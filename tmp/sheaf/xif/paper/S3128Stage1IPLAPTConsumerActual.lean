import tmp.sheaf.xif.paper.IPLAPTActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
namespace LeanFormal.IUT.XiFPaper.S3128Stage1IPLAPTConsumerActual
universe uG uv ua upi umon ui uOut1 uOut2
variable {V : Type uv}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {l : PrimeGeFive}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n n' : Int}
variable {G1 : Type uG} [Group G1] {G1' : Type uG} [Group G1']
variable {G2 : Type uG} [Group G2]
variable {Output1 : Type uOut1} {Output2 : Type uOut2}
variable {S : SourceOneColumnArithmeticHolomorphicStructure V}
variable {A : SourceTheorem311MultiradialAlgorithm G1 G2 I n Output1}
variable {A' : SourceTheorem311MultiradialAlgorithm G1' G2 I n' Output2}
variable {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
variable {upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V}

/-- Stage 1 triangle premise extracted from actual IPL/APT evidence:
the IPL factorization, the Kummer-evaluation two-path equality, and an
actual algorithmic parallel transport. All three are existing source types;
no new Prop field is introduced. -/
def S3128Stage1IPLAPTTrianglePremise
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) : Prop :=
  E.ipl.inputLink = E.ipl.composite ∧
    E.kummerEvaluation.square.domainExpression =
      E.kummerEvaluation.square.codomainExpression ∧
    Nonempty (SourceAlgorithmicParallelTransport S A A')

theorem S3128Stage1IPLAPTTrianglePremise_holds
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    S3128Stage1IPLAPTTrianglePremise E := by
  refine ⟨E.ipl.inputLink_eq_composite,
    E.kummerEvaluation.domainExpression_eq_codomainExpression, ?_⟩
  exact ⟨E.transport⟩

/-- Actual consumer: APT evidence yields the descended quotient equivalence
of the two algorithm instances (the APT transport surface). -/
noncomputable def S3128Stage1APTConsumer_quotientEquiv
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    Quotient (twoActionSetoid A) ≃ Quotient (twoActionSetoid A') :=
  E.toTransport.quotientEquiv

/-- Actual consumer: APT evidence yields the reduced APT statement used by the
second/third triangle. -/
theorem S3128Stage1APTConsumer_statement
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    SourceAPTStatement S A A' :=
  E.aptStatement

#check S3128Stage1IPLAPTTrianglePremise
#check S3128Stage1IPLAPTTrianglePremise_holds
#check S3128Stage1APTConsumer_quotientEquiv
#check S3128Stage1APTConsumer_statement
end LeanFormal.IUT.XiFPaper.S3128Stage1IPLAPTConsumerActual