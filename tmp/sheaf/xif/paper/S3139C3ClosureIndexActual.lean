/-!
# S3139: C3 closure INDEX ids and checklist (data only; registry frozen except approved re-pins)

Records the certified C3 closure artifacts and their INDEX ids for the next
approved re-pin.  Each entry: (index id, declarations, results line, source
SHA-256 prefix, citable-checker verdict).

* INDEX.FT.C3.convention-identification -> RESOLVED THEOREM
  (S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds,
   sourceInd1ConventionComparison, sourceInd1ConventionComparison_tprod,
   conventionFiber, conventionFiberEquiv).
* INDEX.TOOL.piTensorEntryPermute -> S3139ToolsPiTensorEntryPermute
  (piTensorEntryPermute, piTensorEntryPermute_tprod) — manufactured generic tool.
* INDEX.FT.C3.convention-consumer -> S3139C3ConventionRegionConsumerActual
  (sourceInd1Convention_reindex_image) — equality form for route consumers.
* INDEX.FT.C3.convention-cross-check -> S3139C3ConventionCrossCheckActual
  (polyIsoConventions_agree_on_tprod) — consistency cross-check only.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139C3ClosureIndexActual

/-- One INDEX entry of the C3 closure. -/
structure C3ClosureIndexEntry where
  indexId : String
  declarations : List String
  file : String
  resultsLine : Nat
  shaSrc : String
  checker : String

/-- The certified C3 closure INDEX entries. -/
def c3ClosureIndex : List C3ClosureIndexEntry :=
  [ { indexId := "INDEX.FT.C3.convention-identification",
      declarations :=
        [ "sourceInd1ConventionIdentification_holds",
          "sourceInd1ConventionComparison",
          "sourceInd1ConventionComparison_tprod",
          "conventionFiber",
          "conventionFiberEquiv" ],
      file := "S3139C3ConventionClosureActual.lean",
      resultsLine := 151396,
      shaSrc := "69D16A41",
      checker := "CITABLE" },
    { indexId := "INDEX.TOOL.piTensorEntryPermute",
      declarations := [ "piTensorEntryPermute", "piTensorEntryPermute_tprod" ],
      file := "S3139ToolsPiTensorEntryPermute.lean",
      resultsLine := 150781,
      shaSrc := "56F814CA",
      checker := "CITABLE" },
    { indexId := "INDEX.FT.C3.convention-consumer",
      declarations := [ "sourceInd1Convention_reindex_image" ],
      file := "S3139C3ConventionRegionConsumerActual.lean",
      resultsLine := 152269,
      shaSrc := "pending-checker",
      checker := "pending" },
    { indexId := "INDEX.FT.C3.convention-cross-check",
      declarations := [ "polyIsoConventions_agree_on_tprod" ],
      file := "S3139C3ConventionCrossCheckActual.lean",
      resultsLine := 151469,
      shaSrc := "786314A1",
      checker := "CITABLE" } ]

/-- The C3 closure checklist (resolved item + certification status). -/
def c3ClosureChecklist : List (String × String) :=
  [ ("convention identification proved", "yes (no extra hypotheses; paper convention kept)"),
    ("non-circular", "yes (reindex/PrcAutomorphismTensorAction production-defined; polyIsoOfPerm literal; tool generic)"),
    ("axioms", "trio only [propext, Classical.choice, Quot.sound]"),
    ("sorryAx", "none"),
    ("tool manufactured", "piTensorEntryPermute (general)"),
    ("registry status", "folded at 13108 via approved reopen; subsequent re-pins only on real closures") ]

end LeanFormal.IUT.XiFPaper.S3139C3ClosureIndexActual
