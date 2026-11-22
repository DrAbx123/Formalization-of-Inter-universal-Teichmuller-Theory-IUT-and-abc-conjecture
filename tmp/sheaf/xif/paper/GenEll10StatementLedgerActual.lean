import LeanFormal.IUT.Audit.Status

/-! # GenEll10: STATEMENT LEDGER (lattice; STEP 0 prior-art checked)

STEP 0 prior-art: S3131GenEll|GenEllPaperInput|GenEllEquivalenceShape|GenEllShapeStatements|BDClassComposition|BDClassChainTool|IUTIVTheoremAInput|genEll_transfer|GenEllTheorem -> 97 paper hits + vendor 4 -> REUSE existing assets; P0 files GenEll00/01/05/08 already exist (other owners).

Corpus: papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt
(Mochizuki, Arithmetic Elliptic Curves in General Position, Math. J. Okayama
Univ. 52 (2010) 1-28).  Ledger of statements with corpus line ranges, existing Lean
asset, status and classification.  No re-proof; no fake closure.
-/

namespace LeanFormal.IUT.XiFPaper.GenEll10StatementLedgerActual

/-- GenEll statement ledger rows: (id, statement, corpus citation, Lean asset/status). -/
def GenEllStatementLedger : List (String × String × String × String) :=
  [ ("GENELL.def11", "arithmetic line bundles / APic (Def 1.1)", "corpus ~150-180 (paper p.112)", "paper-input; S3131GenEllCorpusCitationsActual cites"),
    ("GENELL.def12", "height ht_{omega_X(D)} and BD-class relations (<~, >~, ~) (Def 1.2)", "corpus ~180-294 (paper p.213)", "P0 ASSET: GenEll01BasicActual.PaperHeight/BDClassOn; IsBDLe reused from S3131BDClassCompositionActual"),
    ("GENELL.ex13", "X(Q)<=d, Galois-finite, compactly bounded subsets K_V (Example 1.3)", "corpus ~231-294 (paper p.231)", "P0 ASSET: GenEll01BasicActual.CompactlyBoundedSubset (abstract)"),
    ("GENELL.def15", "minimal field of definition, reduced divisor, log-different, conductor, log-cond (Def 1.5)", "corpus ~432-505 (paper p.432)", "P0 ASSET: GenEll01BasicActual.PaperLogDiff/PaperLogCond"),
    ("GENELL.prop14", "Prop 1.4 Basic Properties of Heights (+ Rem 1.4.1)", "corpus ~294-423", "P0 ASSET (owner abc GenEll02Prop14Actual, pending)"),
    ("GENELL.prop16", "Prop 1.6 Conductor Bounded by the Height", "corpus ~505-523", "P0 ASSET (owner abc GenEll03Prop16Actual, pending)"),
    ("GENELL.prop17", "Prop 1.7 Conductors and Log Differents", "corpus ~524-604", "P0 ASSET (owner abc GenEll04Prop17Actual, pending)"),
    ("GENELL.thm21", "Theorem 2.1: (i) ABC/Effective Mordell/Vojta for all hyperbolic curves <=> (ii) ABC for Sigma-supported compactly bounded subsets", "corpus 615-687", "P0 ASSET: GenEll05Theorem21Actual (CaseI/CaseII; theorem21_i_implies_ii PROVED; Theorem21_ii_implies_i_required named paper-input; Theorem21ReductionInputs: noncriticalBelyiExists/coverConstruction/bdClassChain/compactlyBoundedData)"),
    ("GENELL.thm21-proof", "(ii)=>(i) proof via noncritical Belyi maps + Prop 1.4/1.6/1.7", "corpus 615-687 + [Mzk1]", "PAPER-PROVED (class B); not formalized; named inputs only"),
    ("GENELL.sec3", "Lemma 3.1 (SL2), 3.2, Rem 3.3.1, Prop 3.4 (Faltings heights), Lemma 3.5-3.7, Theorem 3.8 (general-position full SL2 Galois action)", "corpus 738-1199", "P0 ASSET (owner stage4 GenEll06Section3StatementsActual, pending); Theorem 3.8 deep input paper-input"),
    ("GENELL.sec4", "Lemma 4.1 (prescribed-size primes; GRH condition), Lemma 4.2 (elementary), Cor 4.3/4.4", "corpus 1200-1425", "P0 ASSET (owner stage4 GenEll07Section4StatementsActual, pending); Lemma 4.1 GRH explicitly named"),
    ("GENELL.main-reduction", "ABC(all) <=> ABC(general position) from Thm 2.1 + Thm 3.8 + Cor 4.3/4.4", "corpus §2-§4", "P0 ASSET: GenEll08MainReductionActual.GenEllMainReductionStatement/genEll_mainReduction_shape/GenEllIUTIVSection2Consumer"),
    ("GENELL.iutiv-s2", "IUT IV section 2 consumer: IUT Thm 1.10 + [GenEll] reduction => ABC (replaces Section2.lean [machine-gap])", "LeanFormal/IUT/IUTIV/Estimates/Section2.lean; IUT IV Thm 1.10 corpus p.1255/1363-1385, Thm A, Cor 2.2 p.2426-2505, Cor 2.3 ~2330", "P3 INTEGRATION target (owner stepxi); GenEll08 consumer shape ready"),
    ("GENELL.mzk1", "[Mzk1] Noncritical Belyi Maps statements (Def 1.1/Cor 1.2/Lemmas 2.1-2.4/Thm 2.5/Cor 3.1-3.2)", "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt", "P2 DEEP INPUT (owner stage4); paper-proved external; no Lean formalization") ]

theorem GenEllStatementLedger_length : GenEllStatementLedger.length = 14 := rfl

end LeanFormal.IUT.XiFPaper.GenEll10StatementLedgerActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: GenEll statement ledger. -/
def GenEllStatementLedgerRecord : Obligation :=
  { id := "INDEX.GENELL.statement-ledger"
    source := "corpus GenEll lines 99-1425; coord/GENELL-FORMALIZATION-PLAN.md; GenEll00/01/05/08 (existing P0 assets); S3131GenEll* assets"
    status := VerificationStatus.interface
    note := "GENELL STATEMENT LEDGER (14 rows): definitions Def 1.1/1.2/1.5 + Ex 1.3 (P0 GenEll01 shared assets), Prop 1.4/1.6/1.7 (abc pending), Theorem 2.1 (GenEll05: trivial direction PROVED, (ii)=>(i) named paper-input with 4 inputs), section 3 statements incl. Theorem 3.8 (stage4 pending; deep paper input), section 4 statements incl. Lemma 4.1 GRH (stage4 pending), main reduction (GenEll08 shape) and IUT IV section 2 consumer P3 (stepxi). [Mzk1] P2 statements listed. No re-proof; no fake closure; deep inputs named as paper-input. Corpus line ranges recorded."
    dependsOn := ["GenEll10StatementLedgerActual", "GenEll00NamingActual", "S3131GenEllPaperInputActual"] }

end LeanFormal.IUT.Audit
