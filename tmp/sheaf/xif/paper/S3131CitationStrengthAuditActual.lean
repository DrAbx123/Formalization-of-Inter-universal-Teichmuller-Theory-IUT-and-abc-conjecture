import LeanFormal.IUT.Audit.Status

/-! # S3131 CITATION-STRENGTH AUDIT (Lead assignment; data only)

Classifications: A = definitional/elementary from IUT III section 3.9 definitions
(should be provable now, NOT a real gap); B = proved theorem in the corpus
(formalization target, finite effort); C = convention/definition (no proof needed,
match notation); D = genuinely unproven/external conjecture. -/

namespace LeanFormal.IUT.XiFPaper.S3131CitationStrengthAuditActual

def S3131CitationStrengthTable : List (String × String × String × String) :=
  [ ("(b) UndilatedHeightBound = height/log-volume dictionary bound", "IUT IV Thm A / Thm 1.10 (proved via Cor 3.12 + log-volume computations + GenEll reduction)", "B", "formalization target; proof chain: Cor 3.12 + log-volume computations + [GenEll] Thm 2.1 reduction"),
    ("(c) UndilatedRegionBound = split point bound + unit-region bound", "IUT IV Thm A/Thm 1.10 region-volume side (proved in corpus)", "B", "formalization target; NOT card P; NOT 'GenEll-strength'"),
    ("[GenEll] Theorem 2.1", "papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt lines 615-687: EQUIVALENCE general <=> compactly bounded; proved via noncritical Belyi maps [Mzk1] + Elkies + Prop 1.4/1.7", "B", "reduction theorem; does NOT prove the bound"),
    ("[Mzk1] noncritical Belyi maps", "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt (17908 B)", "B", "proved in corpus; input to GenEll Thm 2.1"),
    ("IUT III Prop 3.9(i)", "IUT III text (corpus); normalization identity", "B", "proved in corpus; used by hull canonical readout"),
    ("IUT III Rem 3.9.4(iv)", "IUT III text (corpus); value-group embedding x |-> x", "C", "convention/normalization identification; match notation in SourceImageRealization"),
    ("IUT III Rem 3.9.5(i)", "IUT III text (corpus); lambda log-degree zero choice", "C", "paper convention; explicit paper input S3135CompletionBaseFieldUnitScalar"),
    ("[AbsTopIII] Proposition 5.8(ii)", "[AbsTopIII] = IUT IV paper; proved in corpus", "B", "proved theorem; formalization target for value-group identification"),
    ("Cor 3.12", "IUT III Cor 3.12 (corpus:10324-10353), proved", "B", "our S3131 canonical QC/HC comparison realizes its conclusion"),
    ("[EtTh]/[NodNon]/[FrdI]/[FrdII]", "corpus references (etale theta / nodal noncritical / frobenioid papers)", "B/C", "per-reference classification pending; none are external conjectures in our dependency chain"),
    ("M2b (q_v = q-parameter of E_F)", "IUT III line 10350 (quantities in terms of q-parameters of E_F); IUT I Def 3.1(b), Ex 3.2(iv); IUT II Def 4.9(viii)", "B/C", "convention link; sharper: M2b = formalization link qVFamily T b = modelTateQ(curve at lifted F-place); norm from q-parameter norm formula; in-model qVFamily := model q => DEFINITIONAL descent (class A in-model)"),
    ("M1 (V_mod_bijection source datum)", "IUT I Def 3.1(b),(e): V_mod_bijection : V_mod ~= V(F) is an explicit SOURCE DATUM (part of initial Theta data), not derivable from arithmetic alone", "C", "source datum; in-model constructible explicitly (V_mod := ULift SourceTheorem311Index + explicit enumeration) => class A in-model; frozen record leaves donor gap") ]

theorem S3131CitationStrengthTable_length : S3131CitationStrengthTable.length = 12 := rfl

def S3131OverclassificationCorrection : List String :=
  [ "RETIRED: vague 'GenEll-strength' label for (b)/(c)",
    "CORRECT: (b),(c) are IUT IV Thm A/Thm 1.10-shape PROVED corpus theorems = formalization targets (class B)",
    "[GenEll] Theorem 2.1 is a REDUCTION (compactly bounded => general), proved in corpus; it does not supply the bound",
    "No residual in the paper route is classified D (genuinely unproven) from this audit so far; class C conventions remain harmless by matching notation",
    "M1 = class C source datum (V_mod_bijection, IUT I Def 3.1(b),(e)); in-model constructible (V_mod := ULift SourceTheorem311Index) => class A in-model; frozen record keeps donor gap",
    "M2b = class B/C convention link (q_v = q-parameter of E_F, IUT III line 10350; I/I Def 3.1(b), Ex 3.2(iv); II Def 4.9(viii)); in-model definitional descent (qVFamily := model q) => class A in-model",
    "NET: none of R1 M1/M2b nor F4.a/F4.b is a genuine external (D) input; all are contract/data/convention clauses (B/C) discharged by construction in the from-scratch model; the abstract frozen-contract theorem keeps them as named structure data" ]

theorem S3131OverclassificationCorrection_length : S3131OverclassificationCorrection.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.S3131CitationStrengthAuditActual