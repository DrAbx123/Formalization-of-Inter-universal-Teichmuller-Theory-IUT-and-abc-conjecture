import LeanFormal.IUT.Audit.Status

/-! # GenEll13: DEPENDENCY MAP (P0 statement layer -> P1/P2/P3 + IUT IV section 2)

Plan: coord/GENELL-FORMALIZATION-PLAN.md.  No re-proof; deep inputs named.
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.GenEll13DependencyMapActual

/-- GenEll dependency rows: (consumer, dependency, required input, status). -/
def GenEllDependencyMap : List (String × String × String × String) :=
  [ ("GenEll05Theorem21Actual", "GenEll01BasicActual", "height/logDiff/logCond/BDClassOn/CompactlyBoundedSubset definitions", "P0 asset (shared)"),
    ("GenEll05Theorem21Actual", "S3131BDClassCompositionActual", "IsBDLe algebra (refl/trans/add_right)", "REUSE; no re-proof"),
    ("GenEll05Theorem21Actual", "[Mzk1] Noncritical Belyi Maps", "noncriticalBelyiExists (Theorem21ReductionInputs)", "P2 deep paper-input (stage4)"),
    ("GenEll05Theorem21Actual", "Prop 1.4/1.6/1.7", "bdClassChain", "P0 abc pending"),
    ("GenEll08MainReductionActual", "GenEll05Theorem21Actual", "Theorem 2.1 equivalence (CaseI/CaseII + proved trivial direction)", "P0 asset"),
    ("GenEll08MainReductionActual", "GenEll06Section3StatementsActual (Theorem 3.8)", "theorem38", "P0 stage4 pending; Theorem 3.8 deep paper-input"),
    ("GenEll08MainReductionActual", "GenEll07Section4StatementsActual (Cor 4.3/4.4)", "cor43/cor44 (Lemma 4.1 GRH)", "P0 stage4 pending"),
    ("GenEll08MainReductionActual", "IUT IV section 2 consumer", "GenEllIUTIVSection2Consumer: bdClassData -> genEllReduction -> abcBound", "P3 stepxi integration; replaces Section2.lean [machine-gap]"),
    ("GenEll12CitationRowsActual", "corpus GenEll + Mzk1 + IUT III/IV", "paper citations (line/page)", "lattice ledger"),
    ("GenEll11IndexIdsActual", "GenEll10/12/13", "INDEX.GENELL ids", "lattice"),
    ("reuse assets", "S3131GenEllPaperInputActual / S3131GenEllInputDetailedActual (GenEllTheorem21) / S3131GenEllEquivalenceShapeActual (reduction_of_equivalence) / S3131GenEllShapeStatementsActual / S3131IUTIVTheoremAInputActual (BDClassInequality) / S3136BDClassChainToolActual", "GenEll statement shape + BD chain", "REUSE (all CITABLE)"),
    ("height layer", "ArithmeticDivisorDegree.lean:1214 heightWeight/:1221/:1225 hTerm; RationalPointDictionary", "ht/logDiff/logCond functions", "REUSE"),
    ("shadow", "S3132IVGenEllShadowAdapterActual.genEll_transfer", "GenEll shadow transfer shape", "REUSE"),
    ("P3.IUTIVSection2-consumer", "GenEll09IUTIVSection2ConsumerActual (stepxi, EXIT0 4824)", "IUT IV section2 consumer with named hypotheses", "REALIZED interface"),
    ("P3.H6-closure", "GenEll10H6ClosureActual", "H6 GenEll closure at INTERFACE level (no paper-general claim)", "REALIZED interface"),
    ("P3.route-interface", "GenEll11RouteInterfaceActual (EXIT0 3758)", "route interface naming H6", "REALIZED interface"),
    ("P3.step0/ids", "GenEll12Step0RecordActual; GenEll13IdsActual.genEllP3Ids (SHA 64A8BD8A)", "STEP 0 record + ids batch", "RECORD") ]

theorem GenEllDependencyMap_length : GenEllDependencyMap.length = 17 := rfl

end LeanFormal.IUT.XiFPaper.GenEll13DependencyMapActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: GenEll dependency map. -/
def GenEllDependencyMapRecord : Obligation :=
  { id := "INDEX.GENELL.dependency-map"
    source := "coord/GENELL-FORMALIZATION-PLAN.md; GenEll05/08; S3131GenEll* assets; ArithmeticDivisorDegree; S3132IVGenEllShadowAdapterActual"
    status := VerificationStatus.interface
    note := "GENELL DEPENDENCY MAP (13 rows): P0 chain GenEll01 -> GenEll05 (Thm 2.1; trivial direction PROVED; reverse needs [Mzk1]+Prop1.4/1.6/1.7) -> GenEll08 (main reduction; needs Thm 3.8 + Cor 4.3/4.4) -> IUT IV section2 consumer (P3 stepxi, replaces Section2.lean machine-gap). Reuse: S3131BDClassCompositionActual (IsBDLe), S3131GenEllPaperInput/InputDetailed/EquivalenceShape/ShapeStatements, S3131IUTIVTheoremAInput, S3136BDClassChainTool, height layer ArithmeticDivisorDegree:1214+, shadow genEll_transfer. Deep inputs named: [Mzk1], Theorem 3.8, Lemma 4.1 GRH. Registry frozen 14041."
    dependsOn := ["GenEll13DependencyMapActual", "GenEll10StatementLedgerActual", "GenEll11IndexIdsActual"] }

end LeanFormal.IUT.Audit