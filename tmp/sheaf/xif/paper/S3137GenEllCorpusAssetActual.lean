import LeanFormal.IUT.Audit.Status

/-! # S3137: GenEll corpus asset (Arithmetic Elliptic Curves in General Position)

CORPUS ASSET, source-only.  Mochizuki, Arithmetic Elliptic Curves in General
Position, Math. J. Okayama Univ. 52 (2010) 1-28; corpus text in
papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt.
Theorem 2.1 (Compactly Bounded Subsets and the ABC Conjecture), corpus lines
615-687: for a finite set Sigma of primes, the following are EQUIVALENT:
(i) Effective Mordell/ABC/Vojta: for every smooth proper geometrically connected
curve X over a number field, reduced divisor D, hyperbolic U_X = complement of D,
positive integer d, epsilon > 0: the BD-class inequality
ht_{omega_X(D)} << (1+epsilon)(log-diff_X + log-cond_D) holds on U_X(Q) <= d;
(ii) ABC Conjecture for Sigma-supported compactly bounded subsets: on the
projective line P with divisor C = {0,1,infty}, for every compactly bounded K_V
subset of U_P(Q) whose support contains Sigma, d, epsilon > 0: the inequality
ht_{omega_P}(C) << (1+epsilon)(log-diff_P + log-cond_C) holds on K_V cap U_P(Q) <= d.
Proof uses noncritical Belyi maps (Mzk1; corpus text
papers/motizuki_corpus/text/Noncritical Belyi Maps.txt).
STRENGTH CLASSIFICATION: Theorem 2.1 is a REDUCTION/EQUIVALENCE theorem, NOT a
proof of ABC; admissible only as paper-input/route-shape reference and for
attribution; it cannot close a residual.  Lean paper-input statement file is
mainline's; this file records the corpus asset and exact citation.
-/

namespace LeanFormal.IUT.XiFPaper.S3137GenEllCorpusAssetActual

/-- GenEll corpus asset: paths, theorem citation, strength classification. -/
def S3137GenEllCorpusAsset : List (String × String) :=
  [ ("path", "papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt"),
    ("paper", "Mochizuki, Arithmetic Elliptic Curves in General Position, Math. J. Okayama Univ. 52 (2010) 1-28"),
    ("theorem", "Theorem 2.1 (Compactly Bounded Subsets and the ABC Conjecture), corpus lines 615-687"),
    ("statement-i", "Effective Mordell/ABC/Vojta: ht_{omega_X(D)} << (1+eps)(log-diff_X + log-cond_D) on U_X(Q) <= d for hyperbolic U_X = X minus D"),
    ("statement-ii", "ABC for Sigma-supported compactly bounded subsets: ht_{omega_P}(C) << (1+eps)(log-diff_P + log-cond_C) on K_V cap U_P(Q) <= d, C = 0 + 1 + infty"),
    ("proof-ingredient", "noncritical Belyi maps; papers/motizuki_corpus/text/Noncritical Belyi Maps.txt (and comments)"),
    ("classification", "REDUCTION/EQUIVALENCE of two ABC forms, NOT a proof of ABC; paper-input/route-shape reference only") ]

/-- Noncritical Belyi Maps corpus asset. -/
def S3137NoncriticalBelyiCorpusAsset : List (String × String) :=
  [ ("path", "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt"),
    ("comments", "papers/motizuki_corpus/text/Noncritical Belyi Maps (comments).txt"),
    ("role", "proof ingredient of GenEll Theorem 2.1 (ii implies i); noncritical Belyi map existence input"),
    ("classification", "PAPER INPUT / corpus reference only; not formalized, not importable; cannot close a residual") ]

end LeanFormal.IUT.XiFPaper.S3137GenEllCorpusAssetActual

namespace LeanFormal.IUT.Audit

/-- INDEX: GenEll corpus asset (reduction reference). -/
def INDEX_PAPER_GENELL : Obligation :=
  { id := "INDEX.PAPER.genell-theorem-2-1"
    source := "papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt lines 615-687 (Theorem 2.1); Noncritical Belyi Maps.txt"
    status := VerificationStatus.interface
    note := "CORPUS ASSET (source-only): GenEll Theorem 2.1 is the EQUIVALENCE between Effective Mordell/ABC/Vojta (i) and ABC for Sigma-supported compactly bounded subsets (ii), proved via noncritical Belyi maps. STRENGTH: REDUCTION theorem, NOT a proof of ABC; usable only as paper-input/route-shape reference and for attribution; cannot close any residual. Coordinate with mainline's Lean paper-input statement file. Registry frozen 14041 (third combined reopen: Option-B model-route closure)."
    dependsOn := ["S3137GenEllCorpusAssetActual"] }

/-- INDEX: noncritical Belyi corpus asset. -/
def INDEX_PAPER_NONCRITICAL_BELYI : Obligation :=
  { id := "INDEX.PAPER.noncritical-belyi-maps"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt (+ comments)"
    status := VerificationStatus.interface
    note := "CORPUS ASSET (source-only): noncritical Belyi maps are the proof ingredient of GenEll Theorem 2.1; paper input, not formalized/importable; cannot close a residual. Attribution recorded in S3137NoncriticalBelyiCorpusAsset."
    dependsOn := ["S3137GenEllCorpusAssetActual"] }

end LeanFormal.IUT.Audit