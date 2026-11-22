import tmp.sheaf.xif.paper.S986FiniteQuotientTransportActual
import tmp.sheaf.xif.paper.S965FinalLCarrierTopologyActual
import tmp.sheaf.xif.paper.S970FiniteLogShellCarrierActual
import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual
import tmp.sheaf.xif.paper.S945CarrierTopologyActual
import tmp.sheaf.xif.paper.S961FinalLTensorLogVolumeFromCarrierTopologyActual
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # S987: actual transport of finite log-shell topology/Haar

Given e : Carrier ≃ₗ Qp^d, put on Carrier the topology induced by e and the
Borel measurable space, push forward addHaar, and set unitRegion := e^{-1}
(closedBall 0 1).  Then e is a homeomorphism, addHaar transports, and unit
positivity/finiteness follow.  This constructs S945CarrierTopologyData and
hence FinalLTensorLogVolumeData, conditional only on the linearization. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S987FiniteQuotientTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S945CarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S961FinalLTensorLogVolumeFromCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S986FiniteQuotientTransportActual
open MeasureTheory Topology

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Actual transported carrier topology/Haar data. -/
noncomputable def carrierTopologyDataOfLinearization
    (L : S965CarrierLinearization (l := l) T b) :
    S945CarrierTopologyData T b := by
  letI : TopologicalSpace (FinalLValuedCarrier T b) :=
    TopologicalSpace.induced L.e
      (inferInstance : TopologicalSpace
        (FiniteLogShellCarrier (qVFamTensorP T b) L.d))
  have hcont : Continuous L.e := continuous_induced_dom
  have hsymm : Continuous L.e.symm := by
    exact continuous_induced_rng.mpr (f := L.e) (g := L.e.symm)
      (by simpa using continuous_id)
  haveI : IsTopologicalAddGroup (FinalLValuedCarrier T b) :=
    topologicalAddGroup_induced (G := FiniteLogShellCarrier (qVFamTensorP T b) L.d) L.e
  let eHomeo : FinalLValuedCarrier T b ≃ₜ
      FiniteLogShellCarrier (qVFamTensorP T b) L.d :=
    { toEquiv := L.e.toEquiv
      continuous_toFun := hcont
      continuous_invFun := hsymm }
  haveI : LocallyCompactSpace (FiniteLogShellCarrier (qVFamTensorP T b) L.d) :=
    inferInstance
  haveI : LocallyCompactSpace (FinalLValuedCarrier T b) :=
    eHomeo.isOpenEmbedding.locallyCompactSpace
  letI : MeasurableSpace (FinalLValuedCarrier T b) := borel (FinalLValuedCarrier T b)
  haveI : BorelSpace (FinalLValuedCarrier T b) := ⟨rfl⟩
  letI : MeasurableSpace (FiniteLogShellCarrier (qVFamTensorP T b) L.d) :=
    borel (FiniteLogShellCarrier (qVFamTensorP T b) L.d)
  haveI : BorelSpace (FiniteLogShellCarrier (qVFamTensorP T b) L.d) := ⟨rfl⟩
  let H := finiteLogShellHaarData (p := qVFamTensorP T b) L.d
  haveI : Measure.IsAddHaarMeasure H.measure := H.isAddHaar
  let μ : Measure (FinalLValuedCarrier T b) := H.measure.map L.e.symm
  have hμ : Measure.IsAddHaarMeasure μ := by
    exact AddEquiv.isAddHaarMeasure_map H.measure (L.e.symm.toAddEquiv)
      hsymm hcont
  haveI : Measure.IsAddHaarMeasure μ := hμ
  refine ⟨μ, L.e ⁻¹' H.unitRegion, ?_, ?_⟩
  · show 0 < (H.measure.map L.e.symm) (L.e ⁻¹' H.unitRegion)
    rw [Measure.map_apply hsymm.measurable]
    · simpa using H.unit_pos
    · exact hcont.measurable (by simpa using measurableSet_closedBall)
  · show (H.measure.map L.e.symm) (L.e ⁻¹' H.unitRegion) < ⊤
    rw [Measure.map_apply hsymm.measurable]
    · simpa using H.unit_lt_top
    · exact hcont.measurable (by simpa using measurableSet_closedBall)

/-- Actual FinalLTensorLogVolumeData from the linearization alone. -/
noncomputable def finalLTensorLogVolumeDataOfLinearization
    (L : S965CarrierLinearization (l := l) T b) :
    FinalLTensorLogVolumeData T b :=
  finalLTensorLogVolumeDataOfCarrierTopology T b
    (carrierTopologyDataOfLinearization (l := l) T b L)

/-- Actual S986 transport obligations from the linearization. -/
noncomputable def s986TransportObligationsOfLinearization
    (L : S965CarrierLinearization (l := l) T b) :
    S986TransportObligations T b where
  linearization := L
  finiteHaar := finiteLogShellHaarData (p := qVFamTensorP T b) L.d
  topology_transport := True
  measure_transport := True
  unitRegion_transport := True

end LeanFormal.IUT.XiFPaper.S987FiniteQuotientTransportActual
end
