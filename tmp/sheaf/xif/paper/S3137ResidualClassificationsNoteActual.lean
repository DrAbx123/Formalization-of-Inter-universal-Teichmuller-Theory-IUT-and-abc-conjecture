import LeanFormal.IUT.Audit.Status

/-! # S3137: residual classification updates per corpus audit (doc/INDEX only)

Lead-ruled classifications (registry frozen 14041 (third combined reopen: Option-B model-route closure); index report only):
(1) INDEX.R1.M2b = Tate-uniformization/q-parameter identification (class B/C
convention link; IUT III:10350; IUT I Def 3.1(b), Ex 3.2(iv)); IN-MODEL
DEFINITIONAL (qVFamily := model q).
(2) INDEX.R1.M1 = V_mod_bijection source datum (class C; IUT I Def 3.1(b),(e));
IN-MODEL CONSTRUCTIBLE (V_mod := ULift SourceTheorem311Index + explicit
placeToMod enumeration; cf. S3137ModelPlaceToModWiringActual).
(3) INDEX.F4.a = class B elementary formalization target (faithfulness proved on
the realified value group; missing only the realified identification).
(4) INDEX.F4.b = contract-data extension + elementary unit-log-zero lemma
(IUT III Rem 3.9.5(i) hull := lambda*O).
shehdd's citation appendix folds mainline's table; no registry edit.
-/

namespace LeanFormal.IUT.Audit

/-- Data: residual classification updates. -/
def S3137ResidualClassifications : List (String × String) :=
  [ ("INDEX.R1.M2b", "Tate-uniformization/q-parameter identification (class B/C convention link; IUT III:10350; IUT I Def 3.1(b), Ex 3.2(iv)); in-model definitional (qVFamily := model q)"),
    ("INDEX.R1.M1", "V_mod_bijection source datum (class C; IUT I Def 3.1(b),(e)); in-model constructible (V_mod := ULift SourceTheorem311Index + explicit placeToMod enumeration; cf. S3137ModelPlaceToModWiringActual)"),
    ("INDEX.F4.a", "class B elementary formalization target (faithfulness proved on the realified value group; missing only the realified identification)"),
    ("INDEX.F4.b", "contract-data extension + elementary unit-log-zero lemma (IUT III Rem 3.9.5(i) hull := lambda times O)") ]

/-- INDEX note: classification updates. -/
def S3137ResidualClassificationsRecord : Obligation :=
  { id := "S3137.index.residual-classifications"
    source := "Lead corpus-audit ruling; IUT I Def 3.1(b), Ex 3.2(iv); IUT III:10350; IUT III Rem 3.9.5(i)"
    status := VerificationStatus.interface
    note := "CLASSIFICATION UPDATES (doc/INDEX only; registry frozen 14041 (third combined reopen: Option-B model-route closure)): M2b class B/C convention link, in-model definitional; M1 class C source datum, in-model constructible; F4.a class B elementary formalization target; F4.b contract-data extension + elementary unit-log-zero lemma (hull = lambda*O). Recorded in S3137ResidualClassifications; consistency/probes unchanged; citations recorded."
    dependsOn := ["S3137ResidualClassifications"] }

end LeanFormal.IUT.Audit