import LeanFormal.IUT.Audit.Status

/-! # S3137: endgame A/B/C/D residual classification (Lead corpus-audit ruling)

Classes: A = definitional/elementary (reductions, in-model constructions,
unit-log-zero lemmas), B = paper-proved formalization targets, C = conventions
(BD-classes, q-parameter), D = genuinely external (none found so far).
Citations from the audit: IUT IV Prop 2.1 p.2334; Cor 2.2(i) p.2404-2428;
reduction p.3117-3155; [GenEll] Thm 2.1 reduction (corpus p.615) and proof;
[Mzk1] statement and proof; IV Thm 1.10 + Steps, Cor 2.2(ii)/(iii), Props 1.4-1.7;
IUT III Rem 3.9.5(i) (hull = lambda*O).  Doc/INDEX only; registry frozen 14041 (third combined reopen: Option-B model-route closure).
-/

namespace LeanFormal.IUT.XiFPaper.S3137ABCDClassificationActual

/-- Class rules with citations. -/
def S3137ABCDClassRules : List (String × String) :=
  [ ("A", "definitional/elementary: IUT IV Prop 2.1 p.2334; Cor 2.2(i) p.2404-2428; reduction p.3117-3155; [GenEll] Thm 2.1 reduction (corpus p.615); [Mzk1] statement; F4.b unit-log-zero (IUT III Rem 3.9.5(i) hull = lambda*O); M2b in-model descent; M1 in-model V_mod_bijection; model skeleton constructs"),
    ("B", "paper-proved formalization targets: IUT IV Thm 1.10 + Steps; Cor 2.2(ii)/(iii); Props 1.4-1.7; [GenEll] Thm 2.1 proof; [Mzk1] proof; F4.a realified identification"),
    ("C", "conventions: BD-classes; q-parameter convention (qVFamily := model q; sameC q/Theta readout)"),
    ("D", "genuinely external: NONE FOUND so far in the audited residual/parent INDEX entries") ]

/-- Per-entry classification (parent registry rows + explicit residuals + tool ids). -/
def S3137ABCDClassOf : List (String × String) :=
  [ ("R1.M0.native-to-OriginalInput", "A"),
    ("R1.M1.bad-tensor-index", "A"),
    ("R1.M2a", "A"),
    ("R1.M2M3M5.sameC-q-theta-readout", "C"),
    ("R1.M2.base-q-transport", "A"),
    ("R1.M2b.tate-q-identification", "A"),
    ("R1.C3-place-tie", "A"),
    ("R1.status-note", "A"),
    ("F4.a.realified-value-group", "B"),
    ("F4.b.paper-scaling-zero", "A"),
    ("F4.b1.haar-uniqueness-scalar-step", "A"),
    ("F4.b1.log-shell-scaling-index", "A"),
    ("ThetaHalf.vform-canonical-residual", "A"),
    ("ThetaHalf.exact-factor-residual", "A"),
    ("ThetaHalf.final-composition", "A"),
    ("first-triangle.A-C", "C"),
    ("FT.C2.conjugate-copy-action", "C"),
    ("FT.C2.reduces-to-M0-M1", "A"),
    ("FT.C2.kummer-artin-pairing", "B"),
    ("FT.C3.convention-identification", "C"),
    ("LGP.residuals", "B"),
    ("INDEX.MODEL.from-scratch-index-arithmetic", "A"),
    ("INDEX.MODEL.from-scratch-theater-family", "A"),
    ("INDEX.MODEL.from-scratch-place-to-mod", "A"),
    ("INDEX.MODEL.place-to-mod-literal", "A"),
    ("INDEX.MODEL.from-scratch-original-input", "A"),
    ("INDEX.MODEL.constant-theater-obstruction", "A"),
    ("INDEX.PAPER-ROUTE.comparison-region", "A"),
    ("INDEX.PAPER-ROUTE.log-shell-point", "B"),
    ("INDEX.PAPER-ROUTE.height-comparison", "B"),
    ("INDEX.PAPER-ROUTE.region-volume-weight", "B"),
    ("INDEX.PAPER-ROUTE.bridge-package", "A"),
    ("INDEX.PAPER-ROUTE.comparison-data-vendor-shape", "A"),
    ("INDEX.PAPER.genell-theorem-2-1", "A"),
    ("INDEX.PAPER.noncritical-belyi-maps", "A"),
    ("INDEX.PAPER.citation-strength-table", "A") ]

end LeanFormal.IUT.XiFPaper.S3137ABCDClassificationActual

namespace LeanFormal.IUT.Audit

/-- INDEX: endgame ABCD classification records. -/
def INDEX_ENDGAME_CLASSIFICATION : Obligation :=
  { id := "INDEX.classification.ABCD-endgame"
    source := "Lead corpus-audit ruling; IUT IV Prop 2.1 p.2334 / Cor 2.2(i) p.2404-2428 / reduction p.3117-3155; [GenEll] Thm 2.1; [Mzk1]; IUT IV Thm 1.10 / Cor 2.2(ii)/(iii) / Props 1.4-1.7; IUT III Rem 3.9.5(i)"
    status := VerificationStatus.interface
    note := "ENDGAME A/B/C/D classification recorded for parent rows, residuals, paper-route fields, model ids, corpus assets: A definitional/elementary (incl. in-model M1/M2b, F4.b unit-log-zero, F4.a elementary part), B paper-proved formalization targets (F4.a realified identification, GenEll/Mzk1 proofs, IV Thm 1.10/Cor 2.2(ii)(iii)/Props 1.4-1.7, LGP/FT.C2-kummer-artin), C conventions (BD-classes, q-parameter/sameC readout, C3 convention), D none found. Doc/INDEX only; registry frozen 14041 (third combined reopen: Option-B model-route closure); consistency/probes unchanged (index files are not gate imports)."
    dependsOn := ["S3137ABCDClassificationActual"] }

end LeanFormal.IUT.Audit