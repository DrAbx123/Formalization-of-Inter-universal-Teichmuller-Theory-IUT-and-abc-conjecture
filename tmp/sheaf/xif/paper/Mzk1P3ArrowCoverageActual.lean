import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3ArrowCoverageActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe uv uG

variable {V : Type uv} {G : Type uG} [Group G] [TopologicalSpace G]

/-- Coverage data for the source arrows: the actual Kummer layer gives a
restriction map on unit Kummer quotients at each place, and every allowed
arrow is covered by this action. -/
structure P3ArrowCoverageData (upper lower : FPrimeStrip V) where
  layer : SourceTimesMuKummerLayer G upper lower
  restriction : ∀ v : V,
    TimesMuQuotient ((upper.Mon v)ˣ) ≃* TimesMuQuotient ((lower.Mon v)ˣ)
  restriction_eq : ∀ v : V, restriction v = (layer.kummer v).equiv
  commutes : ∀ (v : V) (u : TimesMuQuotient ((upper.Mon v)ˣ)),
    restriction v u = (layer.kummer v).equiv u
  coverage : ∀ v : V, Function.Bijective (restriction v)

end LeanFormal.IUT.XiFPaper.Mzk1P3ArrowCoverageActual