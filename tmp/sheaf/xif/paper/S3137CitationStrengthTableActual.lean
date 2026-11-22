import LeanFormal.IUT.Audit.Status

/-! # S3137: paper citation-strength table (audited; corpus text present)

Each entry: corpus file present in papers/motizuki_corpus/text/, exact theorem
citation, and strength classification.  Classes used:
DEFINITIONAL (definitions only), PAPER-PROVED (the paper proves it; genuine
external input to our formalization), FORMALIZATION-TARGET (paper-proved and is
the object of our formalization), GENUINELY-EXTERNAL (math outside the corpus
that would have to be imported/formalized separately).  No registry edit.
-/

namespace LeanFormal.IUT.XiFPaper.S3137CitationStrengthTableActual

/-- [GenEll] Arithmetic Elliptic Curves in General Position. -/
def S3137CitationGenEll : List (String × String) :=
  [ ("corpus", "papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt"),
    ("paper", "Mochizuki, Arithmetic Elliptic Curves in General Position, Math. J. Okayama Univ. 52 (2010) 1-28"),
    ("theorem", "Theorem 2.1 lines 615-687: Effective Mordell/ABC/Vojta <=> ABC for Sigma-supported compactly bounded subsets (via noncritical Belyi maps)"),
    ("strength", "PAPER-PROVED REDUCTION (equivalence of two ABC forms; NOT a proof of ABC); genuinely external to our tree; usable as route-shape/attribution only") ]

/-- [Mzk1] Noncritical Belyi Maps. -/
def S3137CitationMzk1 : List (String × String) :=
  [ ("corpus", "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt; comments in Noncritical Belyi Maps (comments).txt"),
    ("paper", "Mochizuki, Noncritical Belyi Maps"),
    ("theorem", "noncritical Belyi map existence theorem (proof ingredient of GenEll Theorem 2.1)"),
    ("strength", "PAPER-PROVED; GENUINELY-EXTERNAL (not formalized here; cannot close a residual)") ]

/-- [AbsTopIII] Topics in Absolute Anabelian Geometry III. -/
def S3137CitationAbsTopIII : List (String × String) :=
  [ ("corpus", "papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt"),
    ("paper", "Mochizuki, Topics in Absolute Anabelian Geometry III"),
    ("theorem", "Proposition 5.8(ii)"),
    ("strength", "PAPER-PROVED; GENUINELY-EXTERNAL to the current formalization spine; attribution/route reference only") ]

/-- IUT III paper-proved source results (formalization targets). -/
def S3137CitationIUTIII : List (String × String) :=
  [ ("corpus", "papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt"),
    ("theorem", "Proposition 3.9; Remarks 3.9.4, 3.9.5"),
    ("strength", "PAPER-PROVED; FORMALIZATION-TARGET (these are exactly the statements our IUT III nodes formalize/reduce)") ]

/-- IUT IV paper-proved ABC-route results (formalization targets). -/
def S3137CitationIUTIV : List (String × String) :=
  [ ("corpus", "papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt"),
    ("theorem", "Theorem 1.10; Theorem A; Corollaries 2.2, 2.3"),
    ("strength", "PAPER-PROVED; FORMALIZATION-TARGET (the ABC/height route our paper route R1 -> Cor312ToABCBridgeInterface targets)") ]

/-- Audited citation-strength table (data). -/
def S3137CitationStrengthTable : List (String × (List (String × String))) :=
  [ ("[GenEll]", S3137CitationGenEll),
    ("[Mzk1]", S3137CitationMzk1),
    ("[AbsTopIII]", S3137CitationAbsTopIII),
    ("[IUT III Prop 3.9 / Rem 3.9.4 / 3.9.5]", S3137CitationIUTIII),
    ("[IUT IV Thm 1.10 / Thm A / Cor 2.2 / 2.3]", S3137CitationIUTIV) ]

end LeanFormal.IUT.XiFPaper.S3137CitationStrengthTableActual

namespace LeanFormal.IUT.Audit

/-- INDEX/PAPER: citation-strength table (audited corpus citations). -/
def INDEX_PAPER_CITATION_STRENGTH : Obligation :=
  { id := "INDEX.PAPER.citation-strength-table"
    source := "papers/motizuki_corpus/text/ (GenEll, Noncritical Belyi Maps, Topics in Absolute Anabelian Geometry III, IUT III, IUT IV)"
    status := VerificationStatus.interface
    note := "AUDITED CITATION STRENGTH: [GenEll] Thm 2.1 = PAPER-PROVED REDUCTION (ABC-for-compactly-bounded <=> general ABC; NOT a proof of ABC; genuinely external); [Mzk1] = PAPER-PROVED, genuinely external (noncritical Belyi maps); [AbsTopIII] Prop 5.8(ii) = PAPER-PROVED, genuinely external; IUT III Prop 3.9/Rem 3.9.4/3.9.5 and IUT IV Thm 1.10/Thm A/Cor 2.2/2.3 = PAPER-PROVED FORMALIZATION-TARGETS. Corpus files and line citations in S3137CitationStrengthTable. Coordinate with mainline citation table; registry frozen 14041 (third combined reopen: Option-B model-route closure)."
    dependsOn := ["S3137CitationStrengthTableActual"] }

end LeanFormal.IUT.Audit