import tmp.sheaf.n8.closure.C1Components
import tmp.sheaf.n8.closure.C1FromP6Donors
import tmp.sheaf.n8.closure.C1P6DonorsFromContract
import tmp.sheaf.n8.closure.SourceDegreeHullC3
import tmp.sheaf.n8.closure.SourceDegreeFromSource
import tmp.sheaf.n8.closure.SourceDegreeComponents
import tmp.sheaf.n8.closure.NativeContractDatumFromD11
import tmp.sheaf.n8.closure.C1DonorCanonical
import tmp.sheaf.n8.closure.NativeSourceAssembly

/-! # C1/SourceDegree integration gate

Imports and checks the named C1 components, the P6 donor connections, the C3-block unconditional SourceDegree result, and the generic SourceDegree components.
-/

#check LeanFormal.IUT.N8Closure.C1Actual.C1ActualDataComponents
#check LeanFormal.IUT.N8Closure.C1Actual.c1ActualDataOfComponents
#check LeanFormal.IUT.N8Closure.C1Actual.sourceInputBinding_nonempty_of_components
#check LeanFormal.IUT.N8Closure.C1Actual.p6BridgeDonorsExist_iff_nativeOldBindingDonorsExist
#check LeanFormal.IUT.N8Closure.C1Actual.nativeOldBindingDonorsExist_of_contract
#check LeanFormal.IUT.N8Closure.C8.sourceDegreeResidual_iff_actualDegree_eq_BHull_c3
#check LeanFormal.IUT.N8Closure.C8.sourceDegreeResidual_iff_actualDegree_eq_BHull_of_components
#check LeanFormal.IUT.N8Closure.C8.sourceDegreeHullReadoutIdentification_c3
#check LeanFormal.IUT.N8Closure.C8.sourcePaperNormalizedVolumeData
#check LeanFormal.IUT.N8Closure.C8.sourceDegreeResidual_iff_actualDegree_eq_BHull_c3_fromSource
#check LeanFormal.IUT.N8Closure.C8.sourceDegreeResidual_iff_actualDegree_eq_BHull_c3_fromSourceHull
#check LeanFormal.IUT.N8Closure.C1Actual.nativeD11PlaceSelection
#check LeanFormal.IUT.N8Closure.C1Actual.badNativeD11Fintype
#check LeanFormal.IUT.N8Closure.C1Actual.nativeContractDatumExists_of_nativeD11Data
#check LeanFormal.IUT.N8Closure.C1Actual.nativeContractDatumExists_of_nativeD11Split
#check LeanFormal.IUT.N8Closure.C1Actual.C1DonorPackage
#check LeanFormal.IUT.N8Closure.C1Actual.c1ActualData_exists_of_canonicalDonors
#check LeanFormal.IUT.N8Closure.C1Actual.c1DonorPackageExists_iff_nativeOldBindingDonorsExist
#check LeanFormal.IUT.N8Closure.C1Actual.nativeOldC1BridgeOfCanonicalDonors
#check LeanFormal.IUT.N8Closure.C1Actual.nativeBridgeComponent_of_canonicalDonors
#check LeanFormal.IUT.N8Closure.C1Actual.NativeSourceAssembly.toSourceData
#check LeanFormal.IUT.N8Closure.C1Actual.nativeContractDatumExists_of_assembly
#check LeanFormal.IUT.N8Closure.C1Actual.sourceInputBinding_nonempty_of_assembly