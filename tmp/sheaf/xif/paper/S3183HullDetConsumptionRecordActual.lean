/-!
# S3183: S3182 hull/det consumption record for S3180 (data only; pins 14041)

Consumer event (hull -> stepxi): S3180 final consumes hull's
S3182Cor312HullDetAssemblyActual (GREEN/CITABLE 6 decls; hull ledger 08:43,
PRIOR-ART-INDEX 08:42) via the theorem
S3180ConditionalAssemblyActual.conditionalAssembly_with_hullDet (M := M) (I : HullDetAssemblyInputs M) :
Cor312HullDetConclusion M I.theta ∧ Cor312Conclusion (toContract H hqneg) ∧ ABCConjecture.
All HullDetAssemblyInputs fields are consumed inside S3182's cor312_hullDet_conditional.
No consumer-side adapter needed.

Honest scope (hull notes, recorded verbatim-in-substance):
* H2 inputs (hc / per-place PaperRootHullFormulaGap / scalar-match hmatch) are the
  named DATA residuals of the hull identity row; H4 (hH4 : |modelThetaValue M| <= theta)
  is the CardQCMPComparison:50-68 class-B boundary.  S3182's assembly itself is fully
  proved, but it is CONDITIONAL on these named rows by design.
* IPL/SHE/APT remain named interface rows (cor312DeepStepRows), not proof fields.
* Field-scaling side available if needed: S3182Cor312HullDetAssemblyActual.cor312_fieldScaling_component
  (reuses AbsTopIII14 real p-adic scaling law) with explicit positivity/finiteness inputs.
* S3180 final evidence: EXIT0 176409, checker CITABLE 11 decls (src 1E644472 /
  olean 266152 BCE41E33), probe _S3180Probe 176455; ids S3180Mzk1IdsActual (EXIT0
  176502, CITABLE, src BC6F92E3).
**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3183HullDetConsumptionRecordActual

/-- Consumer-event rows: (item, evidence, status). -/
def hullDetConsumptionRecord : List (String × String × String) :=
  [ ("S3182 -> S3180 consumer", "S3180ConditionalAssemblyActual.conditionalAssembly_with_hullDet (M := M)", "CONSUMED (no adapter needed)"),
    ("H2 named data residuals", "HullDetAssemblyInputs.hc / .G (PaperRootHullFormulaGap) / .hmatch", "named DATA residuals (conditional by design)"),
    ("H4 boundary", "HullDetAssemblyInputs.theta/theta_nonneg/hH4; CardQCMPComparison:50-68", "class-B boundary; consumed by S3182"),
    ("IPL/SHE/APT", "S3182.cor312DeepStepRows", "named interface rows (not proof fields)"),
    ("field-scaling option", "S3182.cor312_fieldScaling_component (AbsTopIII14 real p-adic scaling)", "available if S3180 needs it; explicit positivity/finiteness inputs"),
    ("S3180 final pin candidate", "EXIT0 176409; checker CITABLE 11 (1E644472/BCE41E33); probe 176455", "awaiting shehdd final pin"),
    ("ids", "S3180Mzk1IdsActual (EXIT0 176502; CITABLE; BC6F92E3)", "INDEX.S3180.hull-det-consumer recorded") ]

/-- Audit references: (source, reference). -/
def hullDetAuditRefs : List (String × String) :=
  [ ("hull AUDIT_LEDGER", "08:43 consumer event"),
    ("hull PRIOR-ART-INDEX", "08:42 consumer event"),
    ("A71 corpus ranges", "Cor 3.12 statement 10324-10353; Step (xi) 10750-10987; conclusion 10897"),
    ("pins", "registry 14041 / gate 23066 / record 18800") ]

end LeanFormal.IUT.XiFPaper.S3183HullDetConsumptionRecordActual
