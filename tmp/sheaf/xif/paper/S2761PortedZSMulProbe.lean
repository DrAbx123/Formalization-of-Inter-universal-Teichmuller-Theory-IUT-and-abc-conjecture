import tmp.sheaf.xif.paper.S2758FundamentalDomainScalingActual
import tmp.sheaf.xif.paper.S2756FractionalIdealHaarActual

noncomputable section
open MeasureTheory
open scoped Pointwise
open LeanFormal.IUT.XiFPaper.S2758FundamentalDomainScalingActual

namespace LeanFormal.IUT.XiFPaper.S2761PortedZSMulProbe

/-- ZSMul instance of the fundamental-domain scaling law: integer scalar acts
through its real coercion. -/
theorem S2761_haar_zsmul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (n : ℤ) (s : Set E) :
    μ ((n : ℝ) • s) =
      ENNReal.ofReal |(n : ℝ) ^ Module.finrank ℝ E| * μ s :=
  S2758_haar_smul μ (n : ℝ) s

#check S2761_haar_zsmul
#check LeanFormal.IUT.XiFPaper.S2756FractionalIdealHaarActual.S2756IdealHaarVolume_eq
#print axioms S2761_haar_zsmul
#print axioms LeanFormal.IUT.XiFPaper.S2756FractionalIdealHaarActual.S2756IdealHaarVolume_eq

end LeanFormal.IUT.XiFPaper.S2761PortedZSMulProbe
end
