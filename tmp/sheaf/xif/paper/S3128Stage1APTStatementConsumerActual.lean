import tmp.sheaf.xif.paper.IPLAPTActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
namespace LeanFormal.IUT.XiFPaper.S3128Stage1APTStatementConsumerActual
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

theorem S3128Stage1APTStatement_nonempty
    (h : SourceAPTStatement S A A') :
    Nonempty (SourceAlgorithmicParallelTransport S A A') :=
  h

theorem S3128Stage1APTStatement_trans
    (h : SourceAPTStatement S A A') :
    Nonempty (SourceAlgorithmicParallelTransport S A A') :=
  h

#check S3128Stage1APTStatement_nonempty
#check S3128Stage1APTStatement_trans
end LeanFormal.IUT.XiFPaper.S3128Stage1APTStatementConsumerActual