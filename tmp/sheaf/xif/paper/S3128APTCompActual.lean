import tmp.sheaf.xif.paper.IPLAPTActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
namespace LeanFormal.IUT.XiFPaper.S3128APTCompActual
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

/-- Composition consumer: two actual APT evidences over a common middle
instance yield an actual parallel transport from the first to the third.
Uses the proved `SourceAlgorithmicParallelTransport.trans`, no new fields. -/
theorem S3128Stage1APT_comp
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight)
    (E' : APTActualEvidence (G := G) (I := I) (n := n') (n' := n'')
      (S := S) (A := A') (A' := A'') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight) :
    Nonempty (SourceAlgorithmicParallelTransport S A A'') :=
  ⟨E.toTransport.trans E'.toTransport⟩

#check S3128Stage1APT_comp
end LeanFormal.IUT.XiFPaper.S3128APTCompActual