/-! # Stage-4 host: repo treasure-survey report (vendor + local tools)

Data-only survey of the treasure locations relevant to the Stage-4 big task
(theta packet + clause adapter + hull wiring + estimate field (c)).  For each
source: file:line, declaration, and how it is used (adapted / source reference /
importable tool).  Vendor snapshots are SOURCE REFERENCE ONLY (cannot import);
local tool libraries are importable oleans.

LABEL: survey report (not a paper object).  Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136VendorSurveyReportActual

/-- One survey row: location, declaration(s), use. -/
structure LGPTreasureRow where
  location : String
  declarations : String
  use : String

/-- The treasure-survey rows. -/
def lgpTreasureSurvey : List LGPTreasureRow :=
  [ ⟨"vendor/.../1fa6387f.../Iut/Stage1/CorollarySchema.lean:28,55,63,66,81,85",
      "signedPilotLogVolume, Corollary312ComparisonData, thetaPilot, qPilot, corollary312, stage1Comparison",
      "ADAPTED (S3136VendorCor312SchemaAdaptedActual): model Cor312 comparison schema; signed inequality kept as explicit missing data"⟩,
    ⟨"vendor/.../Iut/Stage1/IUTSourceScaffold.lean:25,40,52,64,72",
      "IUTSourceObligationProvider, comparisonData, stage1Comparison, corollary312, audit",
      "source reference for the model SourceDefinition31Data assembly obligations (provider-style staging)"⟩,
    ⟨"vendor/.../Iut/Stage1/IUTStage1FrobenioidShift.lean (81840 lines)",
      "thetaPilotMatchesPackage:2347, qPilotLogVolumeMatchesPackage:2416, qPilotRegion:19564+19824+20071+20472+23920, qPilotLogKummerNonInterference:9612",
      "source reference for the Frobenioid-shift qPilot region/log-volume package; not importable; used to align our theta/q pilot component names"⟩,
    ⟨"vendor/.../Iut/Stage1/IUTStage1Data.lean:...",
      "IUTStage1PreLedgerData, thetaChartTrivial, qSigned_eq_chartedQ, qSigned_le_targetSigned, targetSigned_eq_choiceTargetVolume",
      "source reference for the Cor312 ledger schema (signed/charted q and theta values)"⟩,
    ⟨"vendor/.../Iut/Stage1/IUTStage1IUTIVAlgebra.lean (9968 lines)",
      "IUT IV / GenEll function-level relations",
      "source reference for the IUT IV Section 2 arithmetic form; relevant to estimate field (c) honesty"⟩,
    ⟨"vendor/.../Iut/Stage1/IUTStage1HodgeTheaterSource.lean:...",
      "legacyZeroColumn/OneColumnHodgeTheater, legacy prime strips and history labels",
      "source reference for the model HodgeTheater slot; our concrete theater is from LeanFormal ConcreteInitialThetaCStage"⟩,
    ⟨"vendor/.../Iut/Foundations (173 files, incl Frobenioid.lean)",
      "vendor frobenioid/source foundations",
      "source reference only; our LeanFormal/IUT/Foundations covers the importable layer"⟩,
    ⟨"tmp/archive_sorry_20261028 (l03-g2, l1-f1..f3, n8)",
      "old closure files",
      "source reference for prior closure attempts (not reusable as proofs)"⟩,
    ⟨"tmp/local-cft-port (importable oleans)",
      "PadicField, Brauer (KummerH2/Invariant/KummerCompat), ContinuousKummerTheory (Kummer.Basic/PAdic), Reciprocity",
      "IMPORTED/REUSED: Brauer.exists_root + KummerTheory.Mu in S3136LGPToolReuseRootActual / S3136LGPKummerClassCandidateActual"⟩,
    ⟨"external/flt-lean-recon-*/FLT (source reference only)",
      "Haar measure / HaarChar / Padic Haar",
      "source reference for Haar normalization; our native Haar family uses Mathlib Measure.addHaar"⟩ ]

/-- The survey has 10 rows. -/
theorem lgpTreasureSurvey_length : lgpTreasureSurvey.length = 10 := rfl

#check lgpTreasureSurvey
#check lgpTreasureSurvey_length

end LeanFormal.IUT.XiFPaper.S3136VendorSurveyReportActual