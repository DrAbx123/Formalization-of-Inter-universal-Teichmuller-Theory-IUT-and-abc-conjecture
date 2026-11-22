import LeanFormal.IUT.Audit.Status

/-! # S3193: Mzk1 Lemma 2.4 (G) tail audit (conjugacy invariance + finiteness)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- 2.4 G-tail rows. -/
def S3193Mzk1Lemma24GTailAudit : List (String × String × Nat × Nat × String) := [
  ("Mzk1Lemma24ConjInvarianceActual.lean", "CITABLE", 3, 2047, "probe green"),
  ("Mzk1Lemma24GaloisUnion2Actual.lean", "CITABLE", 3, 2914, "probe green") ]

theorem S3193Mzk1Lemma24GTailAudit_length : S3193Mzk1Lemma24GTailAudit.length = 2 := rfl

/-- Content. -/
def S3193Mzk1Lemma24GTailContent : List String := [
  "ConjInvariance: s3135_minpoly_eq_of_mem_conjugateSet + s3135_reducedDegreeOfPoint_eq_on_conj + s3135_image_pointClosure_eq PROVED (Galois-invariance of minpoly/reduced degree/closed set)",
  "GaloisUnion2: s3135_conjugateSet_finite PROVED + s3135_conjugateSetFiniteStatement PROVED (finite conjugate set) => Lemma2.4 (G) FINITE CLOSED",
  "probes Mzk1Lemma24ConjInvarianceProbeActual/GaloisUnion2ProbeActual EXIT=0 trio",
  "remaining 2.4: (F) f0 coefficient bound, (D) descent, (M) main statement; (G) closed" ]

theorem S3193Mzk1Lemma24GTailContent_length : S3193Mzk1Lemma24GTailContent.length = 4 := rfl

/-- Record. -/
def S3193Mzk1Lemma24GTailAuditRecord : Obligation :=
  { id := "IUT.project.mzk1-lemma24-gtail-audit"
    source := "post-resume audit 2026-11-10 12:50; checker+probes"
    status := VerificationStatus.interface
    note :=
      "MZK1 LEMMA2.4 (G) TAIL: ConjInvariance CITABLE 3 decls (minpoly/reduced-degree "
      ++ "Galois-invariance + image pointClosure eq PROVED); GaloisUnion2 CITABLE 3 decls "
      ++ "(conjugateSet_finite + ConjugateSetFiniteStatement PROVED) => (G) FINITE CLOSED; "
      ++ "remaining (F)/(D)/(M)."
    dependsOn := [ "S3189Mzk1Lemma24UnionAuditRecord" ] }

#check S3193Mzk1Lemma24GTailAuditRecord
#check S3193Mzk1Lemma24GTailAudit_length
#check S3193Mzk1Lemma24GTailContent_length

end LeanFormal.IUT.Audit
