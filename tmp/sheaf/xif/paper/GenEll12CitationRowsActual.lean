import LeanFormal.IUT.Audit.Status

/-! # GenEll12: CITATION ROWS (corpus line ranges / paper pages / classification)

Consolidated citation rows for the GenEll formalization; complements
S3131GenEllCorpusCitationsActual / S3131GenEllInputDetailedActual (existing assets;
no duplication of declarations, this is the lattice ledger).  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.GenEll12CitationRowsActual

/-- Citation rows: (id, paper/corpus, line range/page, theorem, classification). -/
def GenEllCitationRows : List (String × String × String × String × String) :=
  [ ("[GenEll].Def1.1", "Arithmetic Elliptic Curves in General Position (Okayama 52 (2010) 1-28)", "corpus ~150-180; paper p.112", "Def 1.1 arithmetic line bundles / APic", "paper-proved definition; cited"),
    ("[GenEll].Def1.2", "same", "corpus ~180-294; paper p.213", "Def 1.2 height and BD-class relations", "paper-proved definition; P0 GenEll01"),
    ("[GenEll].Ex1.3", "same", "corpus ~231-294; paper p.231", "Example 1.3 X(Q)<=d and compactly bounded subsets", "paper-proved; P0 GenEll01 abstract"),
    ("[GenEll].Def1.5", "same", "corpus ~432-505; paper p.432", "Def 1.5 log-different, conductor, log-cond", "paper-proved definition; P0 GenEll01"),
    ("[GenEll].Prop1.4", "same", "corpus ~294-423", "Prop 1.4 Basic Properties of Heights (+ Rem 1.4.1)", "paper-proved; P0 abc pending"),
    ("[GenEll].Prop1.6", "same", "corpus ~505-523", "Prop 1.6 Conductor Bounded by the Height", "paper-proved; P0 abc pending"),
    ("[GenEll].Prop1.7", "same", "corpus ~524-604", "Prop 1.7 Conductors and Log Differents", "paper-proved; P0 abc pending"),
    ("[GenEll].Thm2.1", "same", "corpus 615-687", "Theorem 2.1 (Compactly Bounded Subsets and the ABC Conjecture) equivalence (i)<=>(ii)", "paper-proved REDUCTION (not ABC proof); P0 GenEll05: (i)=>(ii) PROVED, (ii)=>(i) paper-input"),
    ("[GenEll].Sec3", "same", "corpus 738-1199", "Lemma 3.1/3.2, Rem 3.3.1, Prop 3.4, Lemma 3.5-3.7", "paper-proved; P0 stage4 pending"),
    ("[GenEll].Thm3.8", "same", "corpus 738-1199", "Theorem 3.8 full special linear Galois action", "paper-proved DEEP INPUT (class B); not formalized"),
    ("[GenEll].Sec4", "same", "corpus 1200-1425", "Lemma 4.1 (prescribed-size primes; GRH), Lemma 4.2, Cor 4.3/4.4", "paper-proved; GRH condition explicit; P0 stage4 pending"),
    ("[Mzk1]", "Noncritical Belyi Maps", "corpus file (papers/motizuki_corpus/text/Noncritical Belyi Maps.txt)", "Def 1.1/Cor 1.2/Lemma 2.1-2.4/Thm 2.5/Cor 3.1-3.2", "paper-proved external; P2 deep input"),
    ("[AbsTopIII]", "Topics in Absolute Anabelian Geometry III", "corpus file", "Proposition 5.8(ii)", "paper-proved external"),
    ("IUT-III.Prop3.9", "Inter-universal Teichmuller Theory III", "corpus 6838/6993", "Proposition 3.9", "paper-proved formalization target"),
    ("IUT-III.Rem3.9.4", "same", "corpus ~7151", "Remark 3.9.4", "paper-proved formalization target"),
    ("IUT-III.Rem3.9.5", "same", "corpus 7652-7680", "Remark 3.9.5(i) hull := lambda*O", "paper-proved formalization target"),
    ("IUT-IV.Thm1.10", "Inter-universal Teichmuller Theory IV", "corpus p.1255/1363-1385", "Theorem 1.10", "paper-proved formalization target"),
    ("IUT-IV.ThmA", "same", "corpus section 1", "Theorem A", "paper-proved formalization target"),
    ("IUT-IV.Cor2.2", "same", "corpus p.2426-2505", "Corollary 2.2", "paper-proved formalization target"),
    ("IUT-IV.Cor2.3", "same", "corpus ~2330+", "Corollary 2.3", "paper-proved formalization target"),
    ("vendor.IUTStage1IUTIVAlgebra", "vendor/promachina/snapshots (source reference only, cannot import)", ":8056/:8085 height_le_weighted_logDiff_logCond_minus_lowerBound; :9900 genEll_transfer; :9919 compact_subset_theoremA", "IUT IV algebra shadow", "vendor adapt only") ]

theorem GenEllCitationRows_length : GenEllCitationRows.length = 21 := rfl

end LeanFormal.IUT.XiFPaper.GenEll12CitationRowsActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: GenEll citation rows. -/
def GenEllCitationRowsRecord : Obligation :=
  { id := "INDEX.GENELL.citation-rows"
    source := "corpus GenEll (lines 99-1425) + Noncritical Belyi Maps + AbsTopIII + IUT III/IV corpus; vendor source refs; S3131GenEllCorpusCitationsActual"
    status := VerificationStatus.interface
    note := "GENELL CITATION ROWS (21): [GenEll] Def 1.1/1.2/Ex 1.3/Def 1.5/Prop 1.4/1.6/1.7/Thm 2.1 (615-687)/Sec3/Thm 3.8/Sec4; [Mzk1] statements; [AbsTopIII] Prop 5.8(ii); IUT III Prop 3.9/Rem 3.9.4/Rem 3.9.5(i); IUT IV Thm 1.10/Thm A/Cor 2.2/Cor 2.3; vendor IUTStage1IUTIVAlgebra source refs. Classification: paper-proved definitions/reductions/formalization targets; Thm 2.1 = reduction NOT ABC proof; no fake proof. Registry frozen 14041."
    dependsOn := ["GenEll12CitationRowsActual", "INDEX.PAPER.citation-strength-table", "S3131GenEllCorpusCitationsActual"] }

end LeanFormal.IUT.Audit
