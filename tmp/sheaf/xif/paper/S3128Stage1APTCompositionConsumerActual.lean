import tmp.sheaf.xif.paper.IPLAPTActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
namespace LeanFormal.IUT.XiFPaper.S3128Stage1APTCompositionConsumerActual
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

/-- Consumer: composition of two actual transports gives the reduced APT
statement for the outer pair. -/
theorem S3128Stage1APTCompositionConsumer_statement
    (D1 : SourceAlgorithmicParallelTransport S A A')
    (D2 : SourceAlgorithmicParallelTransport S A' A'') :
    SourceAPTStatement S A A'' :=
  ⟨D1.trans D2⟩

/-- Consumer: two nonempty transports compose to a nonempty outer transport. -/
theorem S3128Stage1APTCompositionConsumer_nonempty
    (h1 : Nonempty (SourceAlgorithmicParallelTransport S A A'))
    (h2 : Nonempty (SourceAlgorithmicParallelTransport S A' A'')) :
    Nonempty (SourceAlgorithmicParallelTransport S A A'') := by
  obtain ⟨D1⟩ := h1
  obtain ⟨D2⟩ := h2
  exact ⟨D1.trans D2⟩

#check S3128Stage1APTCompositionConsumer_statement
#check S3128Stage1APTCompositionConsumer_nonempty
end LeanFormal.IUT.XiFPaper.S3128Stage1APTCompositionConsumerActual