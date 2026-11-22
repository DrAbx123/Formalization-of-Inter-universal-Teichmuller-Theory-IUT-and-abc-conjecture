import LeanFormal.IUT.Audit.Status

/-! # S3207: ported TauCeti Belyi assets record (NON-GATE)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Ported Belyi rows. -/
def S3207PortedBelyiRows : List (String × String × String) := [
  ("TauCeti.Algebra.Polynomial.CriticalValues", "EXIT=0 (ported non-gate)", "src 10151B olean fresh; criticalValues_def/mem_criticalValues/aeval_mem_criticalValues/criticalValues_finite/criticalValues_map/criticalValues_comp_subset etc."),
  ("TauCeti.Algebra.Polynomial.Belyi", "EXIT=0 (ported non-gate)", "src 19283B olean fresh; belyiPolynomial theory (eval/degree/rootSet/derivative) + EXISTS lemmas exists_polynomial_eval_mem_criticalValues_subset (S : Finset Q) and exists_polynomial_aeval_mem_criticalValues_subset (Belyification) — genuine Belyi theorem over critical values"),
  ("record status", "PORTED NON-GATE", "Apache-2.0 attribution retained (TauCeti ff33d5f0); probe _S3207PortedBelyiProbe queued for key lemmas; no gate/registry claims") ]

theorem S3207PortedBelyiRows_length : S3207PortedBelyiRows.length = 3 := rfl

/-- Record. -/
def S3207PortedBelyiRecord : Obligation :=
  { id := "IUT.port.tauceti-belyi-assets"
    source := "qpilot port batch 2026-11-10 18:32; watchdog EXIT=0 + olean fresh"
    status := VerificationStatus.interface
    note :=
      "PORTED BELYI ASSETS (NON-GATE): TauCeti.Algebra.Polynomial.CriticalValues (10151B) + "
      ++ "TauCeti.Algebra.Polynomial.Belyi (19283B), both EXIT=0 with fresh oleans; Belyi file "
      ++ "proves genuine Belyification existence lemmas over critical values "
      ++ "(exists_polynomial_eval/aeval_mem_criticalValues_subset); Apache-2.0 attribution retained. "
      ++ "Recorded as ported non-gate assets for GenEll15/GeometricCore consumers."
    dependsOn := [ "S3203PortedAbcRecord" ] }

#check S3207PortedBelyiRecord
#check S3207PortedBelyiRows_length

end LeanFormal.IUT.Audit
