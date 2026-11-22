import LeanFormal.IUT.Audit.Status

/-! # S3147: bracketed-citation classification audit data (no over-classification)

Verified facts behind the [xxxxx] reclassification audit: which citations are
definitions/elementary, proved-in-corpus (formalization targets), conventions,
or genuinely external.  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (citation, status in repo/corpus, do-not-overclaim note) rows. -/
def S3147CitationFacts : List (String × String × String) := [
  ("[GenEll] Arithmetic Elliptic Curves in General Position", "corpus text PRESENT (papers/motizuki_corpus)", "Thm 2.1 is a PROVED reduction (ABC for compactly bounded subsets <=> general ABC) - NOT a proof of ABC; formalization target (class B)"),
  ("[Mzk1] Noncritical Belyi Maps", "corpus text PRESENT", "available reference; not a machine gap"),
  ("[AbsTopIII] Topics in Absolute Anabelian Geometry III", "corpus text PRESENT; Prop 5.8(ii) proved", "proved in corpus -> formalization target (class B), not external"),
  ("IUT III Prop 3.9", "proved in corpus (text lines 6838/6993)", "formalization target; NOT a gap"),
  ("IUT III Rem 3.9.4", "'elementary observations'", "class A (elementary) - provable now"),
  ("IUT III Rem 3.9.5(i)", "hull := lambda*O definition", "class A/C (definition/convention)"),
  ("IUT IV Thm 1.10 / Thm A / Cor 2.2 / Cor 2.3", "proved in corpus", "formalization targets (class B); no false gap claims") ]

theorem S3147CitationFacts_length : S3147CitationFacts.length = 7 := rfl

/-- Classification taxonomy (A definitional/elementary; B proved-in-corpus; C convention; D external). -/
def S3147CitationClasses : List String := [
  "A = definitional / elementary (provable now)",
  "B = proved in corpus (formalization target, NOT a gap)",
  "C = convention / choice (state explicitly)",
  "D = genuinely external / difficult input (least common)" ]

theorem S3147CitationClasses_length : S3147CitationClasses.length = 4 := rfl

/-- Citation classification audit data record. -/
def S3147CitationClassificationData : Obligation :=
  { id := "IUT.project.citation-classification-audit"
    source := "user challenge on over-classified [xxxxx] citations; Lead survey; papers/motizuki_corpus; LeanFormal/IUT/IUTIV/Estimates/Section2.lean (GenEll reduction refs)"
    status := VerificationStatus.interface
    note :=
      "RECLASSIFICATION AUDIT DATA: [GenEll]/[Mzk1]/[AbsTopIII]/IUT III/IV references are "
      ++ "present in the corpus and mostly PROVED there; [GenEll] Thm 2.1 is a proved EQUIVALENCE "
      ++ "reduction (not a proof of ABC). Taxonomy A (definitional/elementary), B (proved-in-corpus "
      ++ "formalization target), C (convention), D (genuinely external). Rule: NO FALSE GAP CLAIMS; "
      ++ "final table to be folded from mainline's reclassification table into the acceptance "
      ++ "appendices (doc-only, no re-pin)."
    dependsOn := [] }

#check S3147CitationClassificationData
#check S3147CitationFacts_length
#check S3147CitationClasses_length

end LeanFormal.IUT.Audit
