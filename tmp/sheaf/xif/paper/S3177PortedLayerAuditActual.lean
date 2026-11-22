import LeanFormal.IUT.Audit.Status

/-! # S3177: ported FLT/TauCeti layer audit (aggregate + key AG modules)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Ported dir aggregate: (dir, green, red) from results log. -/
def S3177PortedAggregate : List (String × Nat × Nat) := [
  ("flt", 15, 3), ("flt_test", 20, 0), ("flt_th", 67, 8), ("flt_rr_serre", 1, 1),
  ("tauceti2", 63, 106), ("belyi_pair", 5, 20) ]

theorem S3177PortedAggregate_length : S3177PortedAggregate.length = 6 := rfl

/-- Ported key AG modules status rows. -/
def S3177PortedKeyModules : List (String × String) := [
  ("Def_AlgebraicCurve_Repartitions", "GREEN flt/Definitions (5805B; EXIT=0)"),
  ("Def_AlgebraicCurve_DivisorClassGroup", "GREEN flt_test/Definitions (18066B; EXIT=0)"),
  ("Def_AlgebraicCurve_CechSectionsOfDivisor", "GREEN flt_th/Definitions (12349B; EXIT=0)"),
  ("Def_AlgebraicGeometry_TwoChartCech", "GREEN flt_test/Definitions (10778B; EXIT=0)"),
  ("Def_AlgebraicGeometry_CoherentBaseChange", "RED flt_rr_serre/Definitions (EXIT=1; other dirs green copy exists)"),
  ("Def_AlgebraicCurve_AdelicIndex / RiemannRochRows / SerrePairing / FiniteMapData", "ported copies present across flt/flt_core/flt_th/flt_rr_serre/flt_test; status scan pending as queue drains"),
  ("sorry audit", "1949 ported .lean files scanned: ZERO raw sorry hits (no code-level sorry)"),
  ("layer note", "ported modules are the bottom AG layer; reds are imports/API adaptation issues being fixed by porting owners") ]

theorem S3177PortedKeyModules_length : S3177PortedKeyModules.length = 8 := rfl

/-- Ported layer audit record. -/
def S3177PortedLayerAuditRecord : Obligation :=
  { id := "IUT.project.ported-layer-audit"
    source := "results-log aggregate + file scan 2026-11-10 06:33"
    status := VerificationStatus.interface
    note :=
      "PORTED LAYER AUDIT: 1949 ported files, ZERO raw code sorry; green counts flt 15/flt_test "
      ++ "20/flt_th 67/tauceti2 63/belyi_pair 5; reds tauceti2 106/belyi_pair 20/flt_th 8/flt 3/"
      ++ "flt_rr_serre 1 (import/API adaptation, porting owners fixing). Key AG modules green: "
      ++ "Repartitions/DivisorClassGroup/CechSectionsOfDivisor/TwoChartCech; CoherentBaseChange red "
      ++ "in flt_rr_serre copy. Audit continues as queue drains."
    dependsOn := [ "S3177AGProofCompletenessRecord" ] }

#check S3177PortedLayerAuditRecord
#check S3177PortedKeyModules_length

end LeanFormal.IUT.Audit
