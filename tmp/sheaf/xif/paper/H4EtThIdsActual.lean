/-!
# H4/EtTh ids + ENDGAME H-row status update (data only; pins 14041)

* INDEX.ETTH.concrete-bridge -> EtTh07ConcreteBridgeActual:
  EtThConcreteBridgeLevel, etThConcreteBridgeLevel, etThConcreteBridge_sourceFrobenioid_eq_boundary,
  etTh_sourceModel_eq_boundary_model, etThThetaLogVolume, etThThetaLogScale,
  etThConcreteBridgeReuse.  Reuses ConcreteSourceEtaleThetaBridge complete proofs
  (stage/packet/reduction/quotient/generator/theta scale/log-volume/algebraic
  finite theta level + level_* laws) and ConcreteSourceFrobenioidBridge model.
* INDEX.ENDGAME.H4 -> H4HullThetaCertificateActual:
  h4_iqHullRealVolume_le, h4_hull_logVolume_le, h4_exists_hull_eq_ofReal,
  h4_ofReal_le_theta_of_imageSet_lower, h4_nonempty_iff, h4_cor312Conclusion,
  h4Status.  Complete-proof consumer of the frozen Card-AMPL supply
  (CardAMPLThetaBoundSupply.realVolume_le/hull_logVolume_le/exists_hull_eq_ofReal/
  ofReal_le_theta_of_imageSet_lower/nonempty_iff/cor312Conclusion).
ENDGAME H-row status update (mainline ledger wording; no closure claim):
- H1-H6: H6 interface-level closed via GenEll10H6ClosureActual (needs Mzk1 imports for
  paper-level); H4 now has a COMPLETE-PROOF consumer layer (conditional on the
  Card-AMPL supply fields for the actual carrier); H2/H7 remain PARTIAL (owners
  mainline/stage4; see S3132ThetaSideEndgameRowsActual H1-H6 corrected rows);
  H1/H3/H5 rows remain as recorded.
- (b) Mzk1 proofs: GeometricCore assembly remains FROZEN per Lead gate; canonical
  RR/Serde/FiniteMapData/Belyi promotions pending (qpilot) -> assembly uses canonical
  assets as ASSUMED COMPLETE only.
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.H4EtThIdsActual

/-- H4/EtTh ids: (index id, declarations, file). -/
def h4EtThIds : List (String × String × String) :=
  [ ("INDEX.ETTH.concrete-bridge",
      "EtThConcreteBridgeLevel, etThConcreteBridgeLevel, etThConcreteBridge_sourceFrobenioid_eq_boundary, etTh_sourceModel_eq_boundary_model, etThThetaLogVolume, etThThetaLogScale, etThConcreteBridgeReuse",
      "EtTh07ConcreteBridgeActual.lean"),
    ("INDEX.ENDGAME.H4",
      "h4_iqHullRealVolume_le, h4_hull_logVolume_le, h4_exists_hull_eq_ofReal, h4_ofReal_le_theta_of_imageSet_lower, h4_nonempty_iff, h4_cor312Conclusion, h4Status",
      "H4HullThetaCertificateActual.lean") ]

/-- ENDGAME H-row status update: (row, evidence, status). -/
def endgameHStatusUpdate : List (String × String × String) :=
  [ ("H4 hull<=theta", "H4HullThetaCertificateActual (complete-proof consumer of Card-AMPL supply)", "COMPLETE PROOF consumer; GAP = actual-carrier supply fields"),
    ("H6 GenEll transfer", "GenEll10H6ClosureActual (interface-level)", "interface-level; paper-level needs Mzk1 import (class B)"),
    ("H1/H3/H5", "S3132ThetaSideEndgameRowsActual corrected rows", "as recorded (partial/class B)"),
    ("H2", "R2 abstract reduction green; concrete weighted identity indirect", "PARTIAL (mainline/abc)"),
    ("H7", "AbsTopIII14FieldScaling RED + Hull03", "PARTIAL (stage4/mainline)"),
    ("(b) Mzk1/GeometricCore", "GeomCore01StatementActual (statement-only) + canonical assets ASSUMED COMPLETE", "FROZEN by Lead gate; assembly pending canonical promotions") ]

end LeanFormal.IUT.XiFPaper.H4EtThIdsActual
