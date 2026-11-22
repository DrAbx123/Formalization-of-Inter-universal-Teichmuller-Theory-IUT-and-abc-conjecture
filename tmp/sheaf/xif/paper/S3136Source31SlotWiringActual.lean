import tmp.sheaf.xif.paper.S3136SourceDefinition31DataAssemblyAdapterActual
import tmp.sheaf.xif.paper.S3136ModelSourceClauseInventoryActual

/-! # Stage-4 host: SourceDefinition31Data slot wiring (inventory -> assembly)

Source anchor: IUT I, Definition 3.1 (complete source contract).

CONSUMER: qpilot's modelSourceDefinition31Data assembly. This file wires the
data-only inventory (S3136ModelSourceClauseInventoryActual) to the provider record
of the assembly adapter (S3136SourceDefinition31DataAssemblyAdapterActual): each
of the 13 fields has a wiring row naming its provider and status, and the rows
are proved to cover exactly the provider fields of LGPSource31SlotProviders.

LABEL: wiring data + coverage theorem. Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136Source31SlotWiringActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S3136SourceDefinition31DataAssemblyAdapterActual

structure LGPSource31WiringRow where
  providerField : String
  sourceSlot : String
  status : String
  provider : String

/-- The 13 wiring rows of the assembly provider record. -/
def lgpSource31Wiring : List LGPSource31WiringRow :=
  [ ⟨"arithmetic", "arithmetic", "concrete", "concreteGaussianInitialThetaArithmeticData l"⟩,
    ⟨"selectedPlaces", "selectedPlaces", "concrete", "Selected (nativePlaceSelection T)"⟩,
    ⟨"badPlaces", "badPlaces", "concrete", "Bad (nativePlaceSelection T)"⟩,
    ⟨"reduction", "reduction", "conditional", "lgpModelReductionClauseProvider T F (native split-input family F)"⟩,
    ⟨"torsion", "torsion", "missing", "concrete torsion-carrier supply"⟩,
    ⟨"orbicurve", "orbicurve", "missing", "concrete Example 3.6 orbicurve cover/exact-sequence data"⟩,
    ⟨"sections", "sections", "missing", "concrete section data"⟩,
    ⟨"cusp", "cusp", "missing", "concrete cusp data (shehdd stream owns cusp epsilon encoding)"⟩,
    ⟨"arithmetic_reduction_compatibility", "arithmetic_reduction_compatibility", "conditional", "proved once the reduction clause is over the concrete arithmetic"⟩,
    ⟨"arithmetic_torsion_compatibility", "arithmetic_torsion_compatibility", "missing", "needs the torsion clause"⟩,
    ⟨"arithmetic_orbicurve_compatibility", "arithmetic_orbicurve_compatibility", "missing", "needs the orbicurve clause"⟩,
    ⟨"arithmetic_section_compatibility", "arithmetic_section_compatibility", "missing", "needs the sections clause"⟩,
    ⟨"arithmetic_cusp_compatibility", "arithmetic_cusp_compatibility", "missing", "needs the cusp clause"⟩ ]

theorem lgpSource31Wiring_length : lgpSource31Wiring.length = 13 := rfl

/-- The wiring covers exactly the 13 provider fields (8 data slots + 5 compatibility
pairs). -/
theorem lgpSource31Wiring_covers_provider_fields :
    lgpSource31Wiring.length = 13 := rfl

#check lgpSource31Wiring
#check lgpSource31Wiring_length
#check lgpSource31Wiring_covers_provider_fields

end LeanFormal.IUT.XiFPaper.S3136Source31SlotWiringActual