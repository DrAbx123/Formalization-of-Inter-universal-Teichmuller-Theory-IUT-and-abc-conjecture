import tmp.sheaf.xif.paper.IPLAPTActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
namespace LeanFormal.IUT.XiFPaper.S3128Stage1IPLFactorActualAdapted
universe uG uv
variable {V : Type uv}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}

/-- Consumer of the actual IPL factorization: the inverse link is the inverse
of the frozen composite. -/
theorem IPLActual.inverse_eq_composite_symm
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip) :
    L.inverse = L.composite.symm := by
  rw [IPLActual.inverse_inputLink, IPLActual.inputLink_eq_composite]
  rfl

/-- Packaged Stage 1 IPL premise: factorization and inverse consistency. -/
def S3128Stage1IPLPremise
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip) : Prop :=
  L.inputLink = L.composite ∧ L.inverse = L.composite.symm

theorem S3128Stage1IPLPremise_holds
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip) :
    S3128Stage1IPLPremise L :=
  ⟨L.inputLink_eq_composite, L.inverse_eq_composite_symm⟩

/-- Consumer: actual Stage 1 IPL factorization record. -/
def S3128Stage1IPLFactorization
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip) :
    SourceLinkFactorization G intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip :=
  L.toLinkFactorization

theorem S3128Stage1IPLFactorization_factorization
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip) :
    (S3128Stage1IPLFactorization L).inputLink =
      (S3128Stage1IPLFactorization L).composite :=
  L.toLinkFactorization_factorization

#check IPLActual.inverse_eq_composite_symm
#check S3128Stage1IPLPremise_holds
#check S3128Stage1IPLFactorization_factorization
end LeanFormal.IUT.XiFPaper.S3128Stage1IPLFactorActualAdapted