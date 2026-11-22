import tmp.sheaf.n8.closure.NativeSourceAssembly
import tmp.sheaf.n8.closure.NativeC1PaperSource
import tmp.sheaf.n8.closure.SourceDegreePaperSource
import tmp.sheaf.n8.closure.SourceDegreeFromSource
import tmp.sheaf.n8.closure.C7ActualFromSource
import tmp.sheaf.n8.closure.C6ProductVolumeActual
import tmp.sheaf.n8.closure.C1NativeConsumerPaperRoute
import tmp.sheaf.n8.closure.PaperN8NativeC1Adapter

/-!
# Final conditional integration gate

WRITE-ONLY gate; no lake run. This file imports the available end-to-end
conditional packet files and #checks their exported declarations.

Packet-file availability:
* NativeC1PaperSource.lean: present, gated below.
* SourceDegreePaperSource.lean: present, gated below.
* NativeSourceAssembly.lean: present, gated below.
* SourceDegreeFromSource.lean: present, gated below.
* C7ActualFromSource.lean: present, gated below.
* C6ProductVolumeActual.lean: present, gated below.
* Available substitute C1 paper-route files: C1NativeConsumerPaperRoute.lean,
  PaperN8NativeC1Adapter.lean, gated below as available conditional C1 layers.

The absent packet files are NOT imported and no stub is created. All gated
declarations remain conditional on their explicit source fields; this gate
adds no data, no theorem, and no axiom.
-/

noncomputable section

/-! ## NativeSourceAssembly: actual native contract route -/
#check LeanFormal.IUT.N8Closure.C1Actual.nativeContractDatumExists_of_assembly
#check LeanFormal.IUT.N8Closure.C1Actual.assemblyDonors
#check LeanFormal.IUT.N8Closure.C1Actual.assemblyInput
#check LeanFormal.IUT.N8Closure.C1Actual.p6BridgeDonorsOfAssembly
#check LeanFormal.IUT.N8Closure.C1Actual.c1ActualData_nonempty_of_assembly
#check LeanFormal.IUT.N8Closure.C1Actual.sourceInputBinding_nonempty_of_assembly
#check LeanFormal.IUT.N8Closure.C1Actual.NativeSourceAssembly
#check LeanFormal.IUT.N8Closure.C1Actual.NativeSourceAssembly.toSourceData

/-! ## NativeC1PaperSource: complete C1 paper-source packet -/
#check LeanFormal.IUT.N8Closure.NativeC1PaperSource.NativeC1PaperSource
#check LeanFormal.IUT.N8Closure.NativeC1PaperSource.NativeC1PaperSource.input
#check LeanFormal.IUT.N8Closure.NativeC1PaperSource.NativeC1PaperSource.donors
#check LeanFormal.IUT.N8Closure.NativeC1PaperSource.NativeC1PaperSource.nativeOldC1Bridge
#check LeanFormal.IUT.N8Closure.NativeC1PaperSource.NativeC1PaperSource.sourceInputBinding
#check LeanFormal.IUT.N8Closure.NativeC1PaperSource.nativeOldC1Bridge_nonempty_of_packet
#check LeanFormal.IUT.N8Closure.NativeC1PaperSource.sourceInputBinding_nonempty_of_packet

/-! ## SourceDegreePaperSource: complete SourceDegree paper-source packet -/
#check LeanFormal.IUT.N8Closure.C8.SourceDegreePaperSourcePacket
#check LeanFormal.IUT.N8Closure.C8.SourceDegreePaperSourcePacket.paperNormalizedVolumeData
#check LeanFormal.IUT.N8Closure.C8.SourceDegreePaperSourcePacket.c7HullData
#check LeanFormal.IUT.N8Closure.C8.SourceDegreePaperSourcePacket.residual_iff_actualDegree_eq_BHull
#check LeanFormal.IUT.N8Closure.C8.SourceDegreePaperSourcePacket.residual_of_actualDegree_eq_BHull
#check LeanFormal.IUT.N8Closure.C8.SourceDegreePaperSourcePacket.actualDegree_eq_BHull_of_residual

/-! ## SourceDegreeFromSource: concrete C6 from PaperNormalizationSourceData -/
#check LeanFormal.IUT.N8Closure.C8.sourcePaperNormalizedVolumeData
#check LeanFormal.IUT.N8Closure.C8.c8HullLogVolume_c3_eq_normalizedLogVolume_fromSource
#check LeanFormal.IUT.N8Closure.C8.sourceDegreeHullReadoutIdentification_c3_fromSource
#check LeanFormal.IUT.N8Closure.C8.sourceDegreeResidual_iff_actualDegree_eq_BHull_c3_fromSource
#check LeanFormal.IUT.N8Closure.C8.sourceDegreeResidual_of_actualDegree_eq_BHull_c3_fromSource
#check LeanFormal.IUT.N8Closure.C8.actualDegree_eq_BHull_of_sourceDegreeResidual_c3_fromSource

/-! ## C7ActualFromSource: C3 concrete hull obligations and C7 data -/
#check LeanFormal.IUT.N8Closure.C7FromSource.actualB
#check LeanFormal.IUT.N8Closure.C7FromSource.actualCommonHull
#check LeanFormal.IUT.N8Closure.C7FromSource.actual_iqHull_eq
#check LeanFormal.IUT.N8Closure.C7FromSource.actual_haar_pos
#check LeanFormal.IUT.N8Closure.C7FromSource.actual_haar_lt_top
#check LeanFormal.IUT.N8Closure.C7FromSource.C3ConcreteHullObligations
#check LeanFormal.IUT.N8Closure.C7FromSource.C3ConcreteHullObligations.toC7ActualObligations
#check LeanFormal.IUT.N8Closure.C7FromSource.concreteSourceHolomorphicHullData
#check LeanFormal.IUT.N8Closure.C7FromSource.concreteObligationsOfHull
#check LeanFormal.IUT.N8Closure.C7FromSource.concreteSourceHolomorphicHullData_nonempty_iff
#check LeanFormal.IUT.N8Closure.C7FromSource.c3_qPilot_eq_tensorUnit

/-! ## C6ProductVolumeActual: exact primitive projections -/
#check LeanFormal.IUT.N8Closure.C6ProductVolumeActual.ThetaPilotCarrierType
#check LeanFormal.IUT.N8Closure.C6ProductVolumeActual.c6ProductIndex
#check LeanFormal.IUT.N8Closure.C6ProductVolumeActual.c6ProductIndex_finite
#check LeanFormal.IUT.N8Closure.C6ProductVolumeActual.c6ProductLocalField
#check LeanFormal.IUT.N8Closure.C6ProductVolumeActual.c6ProductLocalField_proper
#check LeanFormal.IUT.N8Closure.C6ProductVolumeActual.c6ProductCarrierEquiv
#check LeanFormal.IUT.N8Closure.C6ProductVolumeActual.c6ProductMeasure
#check LeanFormal.IUT.N8Closure.C6ProductVolumeActual.c6ProductFiniteOnCompactsWitness
#check LeanFormal.IUT.N8Closure.C6ProductVolumeActual.c6ProductOpenPosWitness

/-! ## Available C1 paper-route substitutes -/
#check LeanFormal.IUT.N8Closure.C1NativeConsumerPaperRoute.NativeC1PaperRoute
#check LeanFormal.IUT.N8Closure.C1NativeConsumerPaperRoute.nativeC1PaperRoute
#check LeanFormal.IUT.N8Closure.C1NativeConsumerPaperRoute.nativeC1PaperRoute_nonempty
#check LeanFormal.IUT.N8Closure.PaperN8NativeC1Adapter.PaperN8NativeC1Adapter
#check LeanFormal.IUT.N8Closure.PaperN8NativeC1Adapter.paperN8NativeC1Adapter
#check LeanFormal.IUT.N8Closure.PaperN8NativeC1Adapter.paperN8NativeC1Adapter_nonempty

end
