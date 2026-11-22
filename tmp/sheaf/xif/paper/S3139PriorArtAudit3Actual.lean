/-!
# S3139: prior-art audit 3 — Option-B completion assets (policy §7.9; data only)

Lead/lattice reported Option-B complete.  Prior-art check (grep-first):
* tmp/sheaf/xif/paper/S3133M1ConcretePrimeMatchActual.lean (checker CITABLE, 5 decls)
  qpilot M1 concrete donor: S3133ConcreteTensorIndex:50, S3133ConcreteTensorIndexEquiv:53,
  S3133ConcreteTensorPrime_eq_five:58, S3131BadTensorPrimeMatch_concrete:68,
  structure S3133M1ConcreteDonor:79 {index_eq : C3.tensorIndex = Bad; p_eq : C3.p = 5}
  -> REUSE (prime-level M1 match closes on the concrete donor; index_eq/p_eq are the
  exact remaining donor fields).
* tmp/sheaf/xif/paper/S3135TreeModelBaseUnitScalingActual.lean (checker CITABLE, 2 decls)
  s3135_treeModelBaseUnitScaling:17 (fills S3133TreeModelBaseUnitScaling with baseUnit = -1,
  norm one), s3135_treeModelBaseUnitScaling_baseUnit:24, _nontrivial:29
  -> REUSE (abc-side base-unit interface fill; UNCONDITIONAL).
* tmp/sheaf/xif/paper/S3137ModelRouteIdsNoteActual.lean (lattice)
  S3137ModelRouteIds:30 + S3137ModelRouteIdsRecord:45 -> REUSE (INDEX note; pin 14041).
* Model-route evidence already reused in the previous batch (S3133ExistingModelAdaptationActual,
  S3133ModelM1PlaceToModActual, S3135ModelSkeletonInterfaceActual, CardHull, CardAMPL).
DECISION: consume the donor + base-unit fill in the route composition; do NOT re-prove.
PIN CORRECTION: the frozen registry pair is 14041 (third combined reopen applied;
S3131FinalResidualRegistryActual EXIT0 SIZE 14041, src 4AF7EC60, olean 5991A075,
checker CITABLE); my earlier references to 13129 are superseded (correction recorded in
S3139PinCorrectionActual).  shehdd single re-pin pending; no registry edits.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139PriorArtAudit3Actual

/-- Option-B completion prior-art entries: (file:line, names, decision). -/
def optionBPriorArt : List (String × String × String) :=
  [ ("S3133M1ConcretePrimeMatchActual.lean:50-81",
      "S3133ConcreteTensorIndex/ConcreteTensorIndexEquiv/ConcreteTensorPrime_eq_five/S3131BadTensorPrimeMatch_concrete/S3133M1ConcreteDonor",
      "REUSE (concrete donor: prime-level M1 match closes; index_eq/p_eq are exact donor fields)"),
    ("S3135TreeModelBaseUnitScalingActual.lean:17-36",
      "s3135_treeModelBaseUnitScaling/_baseUnit/_nontrivial",
      "REUSE (abc base-unit interface fill, unconditional baseUnit = -1)"),
    ("S3137ModelRouteIdsNoteActual.lean:30/45",
      "S3137ModelRouteIds/S3137ModelRouteIdsRecord", "REUSE (INDEX note; pins 14041)"),
    ("S3139ModelM1DischargeActual.lean:46-104",
      "sourceModelM1Evidence/_holds, firstTriangleRouteResidualModelM1",
      "REUSE (in-model M1 discharge already promoted)") ]

end LeanFormal.IUT.XiFPaper.S3139PriorArtAudit3Actual
