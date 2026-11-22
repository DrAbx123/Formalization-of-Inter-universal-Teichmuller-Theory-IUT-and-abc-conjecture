/-!
# EtTh02: deep theta-function inputs as NAMED class-B D-inputs (proved := false)

The [EtTh] paper's deep results are recorded as exact named inputs with corpus
anchors and status.  They are NOT proved here and must not be counted as closure;
downstream consumers may only use them as explicit hypotheses.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.EtTh02DeepInputsActual

/-- A named deep paper-input: id, exact statement (prose), corpus anchor, status. -/
structure EtThDeepInput where
  id : String
  statement : String
  corpusAnchor : String
  /-- whether this input is proved in the tree (all false at the statement layer) -/
  proved : Bool
  /-- honesty class -/
  klass : String

/-- The [EtTh] deep inputs (all proved := false; class B). -/
def etThDeepInputs : List EtThDeepInput :=
  [ { id := "EtTh.Prop1.1", statement := "Theta Action of the Tempered Fundamental Group", corpusAnchor := "corpus l.784", proved := false, klass := "B" },
    { id := "EtTh.Lemma1.2", statement := "Compatibility of Theta Trivializations", corpusAnchor := "corpus l.1147", proved := false, klass := "B" },
    { id := "EtTh.Prop1.3", statement := "The Étale Theta Class", corpusAnchor := "corpus l.1169", proved := false, klass := "B" },
    { id := "EtTh.Prop1.4", statement := "Relation to the Classical Theta Function", corpusAnchor := "corpus l.1338", proved := false, klass := "B" },
    { id := "EtTh.Prop1.5", statement := "Theta Cohomology", corpusAnchor := "corpus l.1401", proved := false, klass := "B" },
    { id := "EtTh.Thm1.6", statement := "Tempered Anabelian Rigidity of the Étale Theta Function", corpusAnchor := "corpus l.1514", proved := false, klass := "B" },
    { id := "EtTh.Thm1.10", statement := "Constant Multiple Rigidity of the Étale Theta Function", corpusAnchor := "corpus l.1979", proved := false, klass := "B" },
    { id := "EtTh.Prop3.2", statement := "Divisors and Rational Functions on Universal Covers", corpusAnchor := "corpus l.5422", proved := false, klass := "B" },
    { id := "EtTh.Prop3.4", statement := "Divisor and Rational Function Monoids", corpusAnchor := "corpus l.5657", proved := false, klass := "B" },
    { id := "EtTh.Sec4", statement := "General Bi-Kummer Theory", corpusAnchor := "corpus §4", proved := false, klass := "B" } ]

/-- No deep input is marked proved (statement-layer honesty). -/
theorem etThDeepInputs_all_unproved :
    etThDeepInputs.all (fun i => !i.proved) = true := rfl

/-- The deep inputs are exactly 10 named items. -/
theorem etThDeepInputs_length : etThDeepInputs.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.EtTh02DeepInputsActual
