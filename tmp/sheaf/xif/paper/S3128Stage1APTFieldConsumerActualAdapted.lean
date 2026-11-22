import tmp.sheaf.xif.paper.IPLAPTActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
namespace LeanFormal.IUT.XiFPaper.S3128Stage1APTFieldConsumerActualAdapted
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

theorem S3128Stage1APTField_landing
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    SourceLocalizationExpressible S Output2 :=
  E.transport.landing

theorem S3128Stage1APTField_comparison
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    SourceTheorem311TwoActionEquivalence A A' :=
  E.transport.comparison

theorem S3128Stage1APTField_iplLink
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    FPrimeStripEquiv intermediateStrip qPilotStrip :=
  E.iplLink

#check S3128Stage1APTField_landing
#check S3128Stage1APTField_comparison
#check S3128Stage1APTField_iplLink
end LeanFormal.IUT.XiFPaper.S3128Stage1APTFieldConsumerActualAdapted