import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

noncomputable section

namespace LeanFormal.IUT.Theorem311Source

universe uG uv

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uv} {upper lower : FPrimeStrip V}

/-- Precise Kummer/log-volume compatibility on the reduced unit-quotient
carriers. -/
def KummerLogVolumeCompatibility
    (L : SourceTimesMuKummerLayer G upper lower)
    (sourceVolume : ∀ v : V,
      TimesMuQuotient ((upper.Mon v)ˣ) → Real)
    (targetVolume : ∀ v : V,
      TimesMuQuotient ((lower.Mon v)ˣ) → Real) : Prop :=
  ∀ (v : V) (x : TimesMuQuotient ((upper.Mon v)ˣ)),
    sourceVolume v x = targetVolume v ((L.kummer v).equiv x)

end LeanFormal.IUT.Theorem311Source
