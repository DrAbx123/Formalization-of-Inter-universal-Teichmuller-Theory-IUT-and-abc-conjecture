import LeanFormal.IUT.Audit.Status

/-! # S3148: citation-appendix refinement (F4.a / F4.b reclassification)

abc's corpus re-examination refines the bracketed-citation classification for
F4.a/F4.b (doc-only; pins unchanged).  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (residual, refined classification, evidence) rows. -/
def S3148F4CitationRefinement : List (String × String × String) := [
  ("F4.a value-monoid faithfulness", "class B elementary formalization target",
   "faithfulness ALREADY PROVED on the realified value group via normalizedRealifiedPrimePowerHom_degree (= [AbsTopIII] Prop 5.8(ii) content); missing only the elementary identification; target name s3135_valueMonoid_realified_identification"),
  ("F4.b normalized scaling", "contract-data extension + elementary unit-log-zero lemma; NOT a paper hypothesis",
   "unit log-degree zero is elementary (IUT III Rem 3.9.5(i) hull := lambda*O); target name s3135_procession_scaling_unit_degree_zero"),
  ("[GenEll] Thm 2.1", "class B (proved equivalence reduction)",
   "ABC for compactly bounded subsets <=> general ABC; NOT a proof of ABC"),
  ("IUT III Prop 3.9 / Rem 3.9.4 / Rem 3.9.5(i)", "class B / A / A-C",
   "prop proved in corpus; remark elementary; hull definition convention") ]

theorem S3148F4CitationRefinement_length : S3148F4CitationRefinement.length = 4 := rfl

/-- Named decomposition targets announced by abc (data). -/
def S3148NamedF4Targets : List String := [
  "s3135_procession_scaling_unit_degree_zero (F4.b elementary unit-log-zero)",
  "s3135_valueMonoid_realified_identification (F4.a elementary identification)" ]

theorem S3148NamedF4Targets_length : S3148NamedF4Targets.length = 2 := rfl

/-- Citation-appendix refinement record (doc-only; no re-pin). -/
def S3148CitationAppendixRefinement : Obligation :=
  { id := "IUT.project.citation-appendix-refinement-f4"
    source := "Lead citation-audit refinement; abc corpus re-examination; IUT III Rem 3.9.5(i); [AbsTopIII] Prop 5.8(ii)"
    status := VerificationStatus.interface
    note :=
      "REFINED CLASSIFICATION: F4.a = class B elementary formalization target (faithfulness "
      ++ "already proved on the realified value group via normalizedRealifiedPrimePowerHom_degree; "
      ++ "missing only the elementary identification). F4.b = contract-data extension + elementary "
      ++ "unit-log-zero lemma (NOT a paper hypothesis; IUT III Rem 3.9.5(i) hull := lambda*O). "
      ++ "Named targets: s3135_procession_scaling_unit_degree_zero, "
      ++ "s3135_valueMonoid_realified_identification. To be folded into the citation appendix when "
      ++ "mainline's final table lands (doc-only; pins registry 13129 / gate 23066 / record 15501 "
      ++ "unchanged; no re-pin for documentation)."
    dependsOn := [ "S3147CitationClassificationData", "S3147CitationAuditMethod" ] }

#check S3148CitationAppendixRefinement
#check S3148F4CitationRefinement_length
#check S3148NamedF4Targets_length

end LeanFormal.IUT.Audit
