import tmp.sheaf.xif.paper.S3137GenEllCorpusAssetActual
import LeanFormal.IUT.Audit.Status

/-! # S3137: GenEll Theorem 2.1 statement form (paper-input shape, NOT proved)

Corpus: papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt
lines 615-687.  GenEll Theorem 2.1 is the equivalence between:
(i) Effective Mordell/ABC/Vojta form: for every smooth proper geometrically
connected curve over a number field, reduced divisor D, hyperbolic U_X = X minus D,
positive d, epsilon > 0: the BD-class inequality ht << (1+eps)(log-diff + log-cond)
holds on U_X(Q) <= d;
(ii) ABC for Sigma-supported compactly bounded subsets on the projective line with
C = 0 + 1 + infty: ht << (1+eps)(log-diff + log-cond) on K_V cap U_P(Q) <= d.
The formal statement is captured as a DATA structure with the equivalence as a
field: this is the paper-input shape, NOT a theorem and NOT a proof of ABC.
No LeanFormal proof of GenEll exists (0 refs) — class B formalization target.
-/

namespace LeanFormal.IUT.XiFPaper.S3137GenEllStatementFormActual

/-- GenEll Theorem 2.1 statement data: two forms + the paper-proved equivalence
field (paper input; not asserted as a Lean theorem). -/
structure S3137GenEllTheorem21Statement where
  effectiveMordellABCForm : Prop
  compactlyBoundedABCForm : Prop
  paperEquivalence : effectiveMordellABCForm ↔ compactlyBoundedABCForm

/-- The corpus citation/statement inventory (data). -/
def S3137GenEllStatementInventory : List (String × String) :=
  [ ("corpus", "papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt"),
    ("paper", "Mochizuki, Arithmetic Elliptic Curves in General Position, Math. J. Okayama Univ. 52 (2010) 1-28"),
    ("theorem", "Theorem 2.1 (Compactly Bounded Subsets and the ABC Conjecture), lines 615-687"),
    ("form-i", "Effective Mordell/ABC/Vojta: ht << (1+eps)(log-diff + log-cond) on U_X(Q)<=d for hyperbolic U_X = X minus D"),
    ("form-ii", "ABC for Sigma-supported compactly bounded subsets: ht << (1+eps)(log-diff + log-cond) on K_V cap U_P(Q)<=d, C = 0+1+infty"),
    ("proof-ingredient", "noncritical Belyi maps (papers/motizuki_corpus/text/Noncritical Belyi Maps.txt)"),
    ("classification", "PAPER-PROVED REDUCTION/EQUIVALENCE, NOT a proof of ABC; class B paper input; no LeanFormal proof (0 refs)"),
    ("lean-shadow", "S3132IVGenEllShadowAdapterActual.genEll_transfer (shadow adapter, source-only shape)") ]

theorem S3137GenEllStatementInventory_length :
    S3137GenEllStatementInventory.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.S3137GenEllStatementFormActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: GenEll statement form (paper input). -/
def S3137GenEllStatementFormRecord : Obligation :=
  { id := "INDEX.PAPER.genell-statement-form"
    source := "papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt lines 615-687; S3137GenEllCorpusAssetActual; S3132IVGenEllShadowAdapterActual"
    status := VerificationStatus.interface
    note := "GENELL THEOREM 2.1 STATEMENT FORM formalized as DATA (structure S3137GenEllTheorem21Statement with effectiveMordellABCForm, compactlyBoundedABCForm, paperEquivalence field): paper-input shape only, NOT a theorem/proof of ABC. Corpus lines 615-687; class B formalization target; no LeanFormal proof (0 refs). Companion corpus asset INDEX.PAPER.genell-theorem-2-1 + noncritical-belyi-maps."
    dependsOn := ["S3137GenEllStatementFormActual", "S3137GenEllCorpusAssetActual"] }

end LeanFormal.IUT.Audit
