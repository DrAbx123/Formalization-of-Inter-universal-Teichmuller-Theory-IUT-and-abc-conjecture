import LeanFormal.IUT.Audit.Status

/-! # GenEll11: INDEX.GENELL ids (paper-input statement ids + status)

Registry frozen 14041; no registry edits.  These ids are INDEX-level statement
ids for the GenEll formalization (P0-P3 plan).
-/

namespace LeanFormal.IUT.XiFPaper.GenEll11IndexIdsActual

/-- INDEX.GENELL ids with status/class (data). -/
def GenEllIndexIds : List (String × String) :=
  [ ("INDEX.GENELL.def11", "paper-input; cited by S3131GenEllCorpusCitationsActual"),
    ("INDEX.GENELL.def12-height-bdclass", "P0 GenEll01BasicActual.PaperHeight/BDClassOn; IsBDLe reuse S3131BDClassCompositionActual"),
    ("INDEX.GENELL.ex13-compactly-bounded", "P0 GenEll01BasicActual.CompactlyBoundedSubset"),
    ("INDEX.GENELL.def15-logdiff-logcond", "P0 GenEll01BasicActual.PaperLogDiff/PaperLogCond"),
    ("INDEX.GENELL.prop14-heights", "P0 abc GenEll02Prop14Actual (pending); corpus 294-423"),
    ("INDEX.GENELL.prop16-conductor-height", "P0 abc GenEll03Prop16Actual (pending); corpus 505-523"),
    ("INDEX.GENELL.prop17-conductors-logdiff", "P0 abc GenEll04Prop17Actual (pending); corpus 524-604"),
    ("INDEX.GENELL.thm21-statement", "P0 GenEll05Theorem21Actual.CaseI/CaseII; corpus 615-687"),
    ("INDEX.GENELL.thm21-i-implies-ii", "PROVED: GenEll05Theorem21Actual.theorem21_i_implies_ii"),
    ("INDEX.GENELL.thm21-ii-implies-i", "PAPER-INPUT: GenEll05Theorem21Actual.Theorem21_ii_implies_i_required + Theorem21ReductionInputs"),
    ("INDEX.GENELL.sec3-statements", "P0 stage4 GenEll06Section3StatementsActual (pending); Lemma 3.1/3.2/Prop 3.4/Lemma 3.5-3.7/Thm 3.8; corpus 738-1199"),
    ("INDEX.GENELL.thm38-deep-input", "PAPER-INPUT deep: Theorem 3.8 full SL2 Galois action (class B)"),
    ("INDEX.GENELL.sec4-statements", "P0 stage4 GenEll07Section4StatementsActual (pending); Lemma 4.1 (GRH)/4.2/Cor 4.3/4.4; corpus 1200-1425"),
    ("INDEX.GENELL.main-reduction", "P0 GenEll08MainReductionActual.GenEllMainReductionStatement/genEll_mainReduction_shape"),
    ("INDEX.GENELL.iutiv-section2-consumer", "P3 stepxi: GenEll08.GenEllIUTIVSection2Consumer replaces Section2.lean [machine-gap]"),
    ("INDEX.GENELL.mzk1-statements", "P2 stage4: [Mzk1] Noncritical Belyi Maps statements (paper-proved external)"),
    ("INDEX.GENELL.citation-rows", "GenEll12CitationRowsActual (lattice)"),
    ("INDEX.GENELL.statement-ledger", "GenEll10StatementLedgerActual (lattice)"),
    ("INDEX.GENELL.dependency-map", "GenEll13DependencyMapActual (lattice)"),
    ("INDEX.GenEll.P3.IUTIVSection2-consumer", "GenEll09IUTIVSection2ConsumerActual (EXIT0 4824; stepxi)"),
    ("INDEX.GenEll.P3.H6-closure", "GenEll10H6ClosureActual (interface level only)"),
    ("INDEX.GenEll.P3.route-interface", "GenEll11RouteInterfaceActual (EXIT0 3758)"),
    ("INDEX.GenEll.P3.step0", "GenEll12Step0RecordActual"),
    ("INDEX.GenEll.P3.ids-batch", "GenEll13IdsActual.genEllP3Ids (SHA 64A8BD8A)") ]

theorem GenEllIndexIds_length : GenEllIndexIds.length = 24 := rfl

end LeanFormal.IUT.XiFPaper.GenEll11IndexIdsActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: GenEll ids. -/
def GenEllIndexIdsRecord : Obligation :=
  { id := "INDEX.GENELL.ids"
    source := "coord/GENELL-FORMALIZATION-PLAN.md; GenEll00/01/05/08; S3131GenEll* assets; corpus"
    status := VerificationStatus.interface
    note := "INDEX.GENELL ids registered (24 rows, incl. stepxi P3 realized): definitions/basic (P0 GenEll01), Prop 1.4/1.6/1.7 (abc pending), Theorem 2.1 statement + PROVED trivial direction + PAPER-INPUT reverse direction with 4 named inputs, section 3 statements + Theorem 3.8 deep input, section 4 statements + Lemma 4.1 GRH, main reduction shape (GenEll08), IUT IV section2 consumer (P3 stepxi), [Mzk1] statements (P2), citation/ledger/dep-map (lattice). Registry frozen 14041."
    dependsOn := ["GenEll11IndexIdsActual", "GenEll10StatementLedgerActual", "INDEX.GENELL.statement-ledger"] }

end LeanFormal.IUT.Audit