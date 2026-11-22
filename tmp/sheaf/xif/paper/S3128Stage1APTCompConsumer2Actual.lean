import tmp.sheaf.xif.paper.S3128APTCompActual
import tmp.sheaf.xif.paper.IPLAPTActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S3128APTCompActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1APTCompConsumer2Actual
universe uG uv ua upi umon ui uOut1 uOut2 uOut3
variable {V : Type uv}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {l : PrimeGeFive}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n n' n'' : Int}
variable {G1 : Type uG} [Group G1] {G1' : Type uG} [Group G1']
variable {G1'' : Type uG} [Group G1'']
variable {G2 : Type uG} [Group G2]
variable {Output1 : Type uOut1} {Output2 : Type uOut2} {Output3 : Type uOut3}
variable {S : SourceOneColumnArithmeticHolomorphicStructure V}
variable {A : SourceTheorem311MultiradialAlgorithm G1 G2 I n Output1}
variable {A' : SourceTheorem311MultiradialAlgorithm G1' G2 I n' Output2}
variable {A'' : SourceTheorem311MultiradialAlgorithm G1'' G2 I n'' Output3}
variable {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
variable {upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V}

/-- Downstream of U11: two APT evidences compose into the APT statement for the
outer pair. -/
theorem S3128Stage1APTCompConsumer2_statement
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight)
    (E' : APTActualEvidence (G := G) (I := I) (n := n') (n' := n'')
      (S := S) (A := A') (A' := A'') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    SourceAPTStatement S A A'' :=
  S3128Stage1APT_comp E E'

/-- Downstream of U11: explicit nonempty composite transport. -/
theorem S3128Stage1APTCompConsumer2_nonempty
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight)
    (E' : APTActualEvidence (G := G) (I := I) (n := n') (n' := n'')
      (S := S) (A := A') (A' := A'') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    Nonempty (SourceAlgorithmicParallelTransport S A A'') :=
  S3128Stage1APT_comp E E'

#check S3128Stage1APTCompConsumer2_statement
#check S3128Stage1APTCompConsumer2_nonempty
end LeanFormal.IUT.XiFPaper.S3128Stage1APTCompConsumer2Actual