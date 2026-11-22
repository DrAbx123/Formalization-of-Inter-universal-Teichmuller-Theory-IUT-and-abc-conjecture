import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual

/-! # Stage-4 host: inventory of the SourceDefinition31Data slots for the model

Source anchors: IUT I, Definition 3.1 (complete source contract: arithmetic,
selected/bad places, reduction, torsion, orbicurve, sections, cusp, and the five
arithmetic-compatibility pairs).

CONSUMER: qpilot's modelSourceDefinition31Data/modelOriginalInput assembly.  This
data-only inventory records, slot by slot, the exact field type, the current
inhabitant status and the provider/owner, so the skeleton can be assembled from
actual inhabitants where they exist and from the named exact missing data
elsewhere.  No opaque Props; statuses are strings, providers are file/declaration
names.

LABEL: data inventory (not a paper object).  Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseInventoryActual

/-- One SourceDefinition31Data slot row. -/
structure LGPSource31Slot where
  /-- field name -/
  field : String
  /-- exact Lean field type (as in SourceDefinition31Boundary.SourceDefinition31Data) -/
  fieldType : String
  /-- 'concrete' | 'conditional' | 'missing' -/
  status : String
  /-- provider or exact-missing provider -/
  provider : String

/-- The inventory of the model SourceDefinition31Data slots. -/
def lgpSource31Inventory : List LGPSource31Slot :=
  [ ⟨"arithmetic", "InitialThetaArithmeticData l", "concrete",
      "concreteGaussianInitialThetaArithmeticData l (ConcreteFinitePlaceBoundary.lean:25)"⟩,
    ⟨"selectedPlaces", "Type u (Selected (nativePlaceSelection T))", "concrete",
      "Selected (nativePlaceSelection T) from a concrete T"⟩,
    ⟨"badPlaces", "Type u (Bad (nativePlaceSelection T))", "concrete",
      "Bad (nativePlaceSelection T) from a concrete T (Fintype instance)"⟩,
    ⟨"reduction", "SourceReductionClause selectedPlaces badPlaces", "conditional",
      "nativeReductionClause T (nativeBadLift T) from a split-input family"⟩,
    ⟨"torsion", "SourceTorsionClause l", "missing",
      "concrete torsion-carrier supply (S2828/S2833/S2843 conditional shapes)"⟩,
    ⟨"orbicurve", "SourceOrbicurveClause", "missing",
      "concrete orbicurve cover/exact-sequence data for the Example 3.6 stage"⟩,
    ⟨"sections", "SourceSectionClause", "missing",
      "concrete section data for the Example 3.6 stage"⟩,
    ⟨"cusp", "SourceCuspClause", "missing",
      "concrete cusp data (shehdd stream owns cusp epsilon real encoding)"⟩,
    ⟨"arithmetic_reduction_compatibility",
      "Prop + proof (reduction clause over the concrete arithmetic)", "conditional",
      "proved once the reduction clause is built over the concrete arithmetic"⟩,
    ⟨"arithmetic_torsion_compatibility", "Prop + proof", "missing",
      "needs the torsion clause above"⟩,
    ⟨"arithmetic_orbicurve_compatibility", "Prop + proof", "missing",
      "needs the orbicurve clause above"⟩,
    ⟨"arithmetic_section_compatibility", "Prop + proof", "missing",
      "needs the sections clause above"⟩,
    ⟨"arithmetic_cusp_compatibility", "Prop + proof", "missing",
      "needs the cusp clause above"⟩ ]

/-- The inventory has 13 rows (the 8 data fields plus the 5 compatibility pairs). -/
theorem lgpSource31Inventory_length : lgpSource31Inventory.length = 13 := rfl

#check lgpSource31Inventory
#check lgpSource31Inventory_length

end LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseInventoryActual