/-! # AbsTopIII02LocalVolumesActual — [AbsTopIII] Prop 5.7 / Cor 5.10 volume-side statements

STEP 0 prior-art (deep search 2026-11-10: query 'Local Volumes|localVolume|log-volume|
arithmetic log-volume|p-adic volume|additive Haar|log-shell|Prop 5.7|Cor 5.10' ->
LeanFormal 632 hits; key: Loadations/Volumes/HaarLogVolume.lean:11 logClosedBallVolume,
:17 addHaar_closedBall_unit_pos, :29 logClosedBallVolume_smul, :45
addHaar_logClosedBallVolume_smul; Foundations/Volumes/WeightedVolume.lean:20
WeightedValues/average; ABCBridge/Bridge/ThetaBoundToHeightWeight.lean; our
S3136NativeHaarFamilyActual/lgpNativeHaarFamily; tmp/local-cft-port PadicField;
vendor IUTStage1HodgeSHE:3996/:4017 (two-sided comparisons).

PAPER: Mochizuki, Topics in Absolute Anabelian Geometry III, §5.  Corpus:
papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt;
Prop 5.7 lines 7915-8020; Cor 5.10 lines 8494-8618.

ALIGNMENT: this ledger refines lattice's AbsTopIII10StatementLedgerActual (C/D/B No volume theorem
is claimed as proved here; the reuse/reduction plan is recorded per row. -/

namespace LeanFormal.IUT.XiFPaper.AbsTopIII02LocalVolumesActual

structure AbsTopIIIStatementRow where
  label : String
  lineRange : String
  content : String
  classification : String

def absTopIIILocalVolumeStatements : List AbsTopIIIStatementRow :=
  [ ⟨"Prop 5.7 (i)(a)", "7915-7935", "k mixed-characteristic nonarchimedean local field, m_k <= O_k maximal ideal, M(k) compact open subsets: there exists a UNIQUE map mu_k : M(k) -> R_{>0} with (1) additivity mu_k(A u B)=mu_k(A)+mu_k(B) for disjoint A,B; (2) translation invariance mu_k(A+x)=mu_k(A), x in k; (3) normalization mu_k(O_k)=1. mu_k is the volume on k; mu_k^log := log(mu_k) is the log-volume; if residue field has cardinality p^f then mu_k^log(m_k^n) = -f*n*log(p) for n in Z.", "C-CONCRETE-FORMALIZABLE (per lattice ledger AbsTopIII10StatementLedgerActual; class A here): normalized additive Haar measure on the locally compact additive group k (Mathlib Measure.addHaar + normalization); formula from Haar scaling on the maximal ideal; reusable template: LeanFormal/IUT/Foundations/Volumes/HaarLogVolume.lean:11-45"⟩,
    ⟨"Prop 5.7 (i)(b)", "7938-7951", "x in k^×, muDot_k(x) := mu_k(x*O_k), muDot_k^log(x) := log(muDot_k(x)): for A in M(k), mu_k^log(x*A) = mu_k^log(A) + muDot_k^log(x); in particular for x in O_k^×, mu_k^log(x*A) = mu_k^log(A).", "C-CONCRETE-FORMALIZABLE (per lattice ledger; class A here): Haar translation/scale invariance; muDot formula from ball scaling"⟩,
    ⟨"Prop 5.7 (i)(c)", "7952-7960", "log_k : O_k^× -> k the p-adic logarithm; A <= O_k^× open such that log_k induces a bijection A -> log_k(A): then mu_k^log(A) = mu_k^log(log_k(A)).", "C-CONCRETE-FORMALIZABLE WITH EFFORT (per lattice ledger; class A/B here): p-adic log analytic bijection on 1+4Z_p-type domains; Mathlib p-adic log API + Haar; the open-set statement needs care"⟩,
    ⟨"Prop 5.7 (ii)(a)", "7961-8005", "k complex archimedean: decomposition k^× = O_k^× x R_{>0}, O_k^× = S^1; M(k) (resp. Mbreve(k)) nonempty compact subsets with projection to R (resp. O_k^×) a compact closure-of-interior subset. The standard absolute value determines a Riemannian (and Kahler) metric on k restricting to metrics on O_k^× and R_{>0}; integrating yields mu_k : M(k)->R_{>0} (resp. muB_k on Mbreve) with (1) additivity for disjoint projections; (2) normalization mu_k(O_k)=1 (resp. muB_k(O_k^×)=2*pi). mu_k^log := log mu_k (resp. muB^log) are radial (resp. angular) log-volumes.", "B-PARTIAL (per lattice ledger; archimedean Riemannian geometry/Kahler metric; Mathlib has complex analysis but no Riemannian measure normalization O_k=1 (radius 1 sqrt2/..); formalizable with effort, not now"⟩,
    ⟨"Prop 5.7 (ii)(b)", "8006-8020", "x in k^×: for A in M(k) (resp. Mbreve(k)), mu_k^log(x*A) = mu_k^log(A)+muDot_k^log(x) (resp. angular version muB_k^log(x*A)=muB_k^log(A)); in particular x in O_k^× gives invariance.", "B-PARTIAL (follows from the archimedean volume once constructed)"⟩,
    ⟨"Cor 5.10 (i)", "8587-8593", "Finite Log-volume: for each •-shell-container S, S^Gal carries a well-defined log-volume (resp. radial/angular log-volumes) depending only on the •-shell-container structure; the •-log-shell is contained in S^Gal and is of finite log-volume.", "C-STATEMENT-LAYER / D-IMPLEMENTATION (per lattice ledger: Cor 5.10 statement is concrete-formalizable; full category-theoretic setup is anabelian-deep): the FINITE statement is the exact consumer of Prop 5.7 uniqueness)"⟩,
    ⟨"Cor 5.10 (ii)", "8594-8598", "Log-Frobenius Compatibility of Log-volumes: the log-volume (resp. radial) computed at the vertex v of the shell-arrow is compatible relative to log-homotopy with the log-volume (resp. angular) computed at the adjacent vertex.", "C-STATEMENT-LAYER / D-IMPLEMENTATION (compatibility statement; uses Prop 5.7 (i)(c)/(ii))"⟩,
    ⟨"Cor 5.10 (iv)", "8602-8618", "Mono-analyticization: •⊢-shell-container structures and the well-defined log-volumes on the associated Gal-superscripted modules; these depend only on the mono-analyticized data (D⊢).", "C-STATEMENT-LAYER / D-IMPLEMENTATION (mono-analyticization statement; consumer for IUT IV §1 log-volume computations)"⟩ ]

theorem absTopIIILocalVolumeStatements_length : absTopIIILocalVolumeStatements.length = 8 := rfl

#check absTopIIILocalVolumeStatements
#check absTopIIILocalVolumeStatements_length

end LeanFormal.IUT.XiFPaper.AbsTopIII02LocalVolumesActual