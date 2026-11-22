import tmp.sheaf.xif.paper.S3136LGPJvLocalTransportActual

/-! # Stage-4 host: local J_v generator range

Source anchors: IUT III, Prop. 3.7, (ii), (v) (pp. 108--112).

This file records the range of the actual local generator transport:
* lgpRootZPowerHom_range_subset: the range lies in the actual theta-value
  subgroup (unit-side J_v candidate);
* qVAlgClosedUnit_mem_range: the actual q_v unit lies in the range (principal
  q_v compatibility).

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPJvLocalTransportRangeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalMonoidActual
open LeanFormal.IUT.XiFPaper.S3136LGPJvPacketTransportActual
open LeanFormal.IUT.XiFPaper.S3136LGPJvLocalTransportActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The range of the local generator transport lies in the theta-value subgroup. -/
theorem lgpRootZPowerHom_range_subset (b : Bad (nativePlaceSelection T)) :
    Set.range (lgpRootZPowerHom T b) ⊆
      (lgpThetaValueSubgroup T b :
        Set (AlgebraicClosure (Completion (qVPlace T b)))ˣ) := by
  rintro _ ⟨m, rfl⟩
  exact lgpRootZPowerHom_mem_thetaValueSubgroup T b m

/-- The actual q_v unit lies in the range of the local generator transport. -/
theorem qVAlgClosedUnit_mem_range (b : Bad (nativePlaceSelection T)) :
    qVAlgClosedUnit T b ∈ Set.range (lgpRootZPowerHom T b) :=
  ⟨Multiplicative.ofAdd ((2 * l.value : ℕ) : ℤ), lgpRootZPowerHom_twoL T b⟩

#check lgpRootZPowerHom_range_subset
#check qVAlgClosedUnit_mem_range

end LeanFormal.IUT.XiFPaper.S3136LGPJvLocalTransportRangeActual
end