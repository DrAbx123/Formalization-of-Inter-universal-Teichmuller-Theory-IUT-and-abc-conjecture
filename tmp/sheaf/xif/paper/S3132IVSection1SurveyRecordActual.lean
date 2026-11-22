set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# IUT IV Section 1 log-volume dictionary survey (UndilatedHeightBound target)

Survey record for the (b) class B target attempt requested by the Lead.
Findings:
* LeanFormal/IUT/IUTIV/Estimates/Section1.lean declares iutIVSection1 : Obligation
  (line 93), iutIVProp17_betaAvg (115), iutIVProp17_lambdaE_pow (119),
  iutIVProp17_weightedTupleSum (125), iutIVProp17_betaTupleSum (157),
  iutIVProp17_middle (172), iutIVProp17_value (186), iutIVProp17 (199) — these
  are the IUT IV Section 1 beta/lambda average estimates (Prop 1.7), NOT a
  log-volume dictionary;
* LeanFormal/IUT/IUTIV/Estimates/Section2.lean exists (Section 2 estimates);
* NO declaration named UndilatedHeightBound exists in LeanFormal/IUT/IUTIV (grep),
  and NO 'undilated'/'log-volume dictionary' phrase occurs in
  papers/motizuki_corpus/text (grep) — the requested named target is NOT present
  in the repo or corpus as such; the (b) work would be new text-derived
  formalization, not a consumer of an existing dictionary file.
Machine-checkable record below; data only.  Registry frozen 13129.
-/

namespace LeanFormal.IUT.XiFPaper.S3132IVSection1SurveyRecordActual

/-- A surveyed IUT IV declaration/annotation. -/
structure IVSectionRecord where
  location : String
  declarations : List String
  relevance : String

/-- The IUT IV Section 1/2 survey entries. -/
def iutIVSectionSurvey : List IVSectionRecord :=
  [ { location := "LeanFormal/IUT/IUTIV/Estimates/Section1.lean:93-199",
      declarations := ["iutIVSection1", "iutIVProp17_betaAvg",
        "iutIVProp17_lambdaE_pow", "iutIVProp17_weightedTupleSum",
        "iutIVProp17_betaTupleSum", "iutIVProp17_middle",
        "iutIVProp17_value", "iutIVProp17"],
      relevance := "Section 1 beta/lambda average estimates (Prop 1.7); no log-volume dictionary" }
  , { location := "LeanFormal/IUT/IUTIV/Estimates/Section2.lean",
      declarations := ["Section 2 estimates"],
      relevance := "Section 2 estimates; no UndilatedHeightBound declaration" }
  , { location := "grep LeanFormal/IUT/IUTIV: UndilatedHeightBound|logVolumeDictionary|undilated",
      declarations := [],
      relevance := "NEGATIVE: no such declaration; (b) class B target absent as named object" }
  , { location := "grep papers/motizuki_corpus/text: UndilatedHeightBound|undilated|log-volume dictionary",
      declarations := [],
      relevance := "NEGATIVE: phrase absent from corpus text" } ]

/-- The survey records four entries. -/
theorem iutIVSectionSurvey_length : iutIVSectionSurvey.length = 4 := rfl

/-- Negative finding: no UndilatedHeightBound declaration surfaces from the survey. -/
def undilatedHeightBoundAbsent : Bool := true

/-- The absence flag is recorded as true (negative result; no invented target). -/
theorem undilatedHeightBoundAbsent_eq : undilatedHeightBoundAbsent = true := rfl

#check IVSectionRecord
#check iutIVSectionSurvey
#check iutIVSectionSurvey_length
#check undilatedHeightBoundAbsent_eq

end LeanFormal.IUT.XiFPaper.S3132IVSection1SurveyRecordActual