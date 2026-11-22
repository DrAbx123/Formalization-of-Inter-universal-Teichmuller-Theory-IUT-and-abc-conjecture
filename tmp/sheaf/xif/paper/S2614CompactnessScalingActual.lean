import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.OModuleCompactnessLayer
import tmp.sheaf.xif.paper.S2611SignedGap2SourceActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2614CompactnessScalingActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S2614_compactnessScalingLogDegreeZero (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (C : I.SourceOneCircUCompactness v R n) :
    I.sourceLocalLogDegree v
      (I.sourceOModuleCompactness_haarData v R n C).scaling = 0 := by
  rw [I.sourceOModuleCompactness_haarData_scaling]
  exact I.sourceLocalLogDegree_one v

def ScalingLogDegreeBounded (D : I.SourceUnitRegionHaarData v R n) : Prop :=
  ∃ C : Real, |I.sourceLocalLogDegree v D.scaling| <= C

def HullDegreeLowerBound (hull : Set (I.ThetaPilotPoint v)) : Prop :=
  ∃ C : Real, ∀ x : I.ThetaPilotPoint v, x ∈ hull ->
    C <= I.sourceLocalLogDegree v x

theorem S2614_compactnessScalingLogDegreeBounded (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (C : I.SourceOneCircUCompactness v R n) :
    ScalingLogDegreeBounded (I := I)
      (I.sourceOModuleCompactness_haarData v R n C) := by
  refine ⟨0, ?_⟩
  rw [S2614_compactnessScalingLogDegreeZero I v R n C]
  simp

#check S2614_compactnessScalingLogDegreeZero
#check S2614_compactnessScalingLogDegreeBounded
#check ScalingLogDegreeBounded
#check HullDegreeLowerBound

end LeanFormal.IUT.XiFPaper.S2614CompactnessScalingActual
end