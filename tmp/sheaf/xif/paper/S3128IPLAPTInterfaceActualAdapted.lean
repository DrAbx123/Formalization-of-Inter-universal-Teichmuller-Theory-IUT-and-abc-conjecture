import tmp.sheaf.xif.paper.IPLAPTActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
namespace LeanFormal.IUT.XiFPaper.S3128IPLAPTInterfaceActualAdapted
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

/-- APT transport computation law exposed from actual evidence. -/
theorem S3128Stage1APT_quotientEquiv_mk
    (E : APTActualEvidence (G := G) (I := I) (n := n) (n' := n')
      (S := S) (A := A) (A' := A') intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight)
    (o : Output1) :
    E.toTransport.quotientEquiv (Quotient.mk (twoActionSetoid A) o) =
      Quotient.mk (twoActionSetoid A')
        (E.toTransport.comparison.outputEquiv o) :=
  E.toTransport.quotientEquiv_mk o

/-- IPL factorization and inverse compatibility packaged without new fields. -/
theorem S3128Stage1IPL_compat_and_inverse
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip) :
    L.inputLink = L.composite ∧
      L.inverse = L.composite.symm := by
  refine ⟨L.inputLink_eq_composite, ?_⟩
  rw [IPLActual.inverse_inputLink, IPLActual.inputLink_eq_composite]
  rfl

#check S3128Stage1APT_quotientEquiv_mk
#check S3128Stage1IPL_compat_and_inverse
end LeanFormal.IUT.XiFPaper.S3128IPLAPTInterfaceActualAdapted