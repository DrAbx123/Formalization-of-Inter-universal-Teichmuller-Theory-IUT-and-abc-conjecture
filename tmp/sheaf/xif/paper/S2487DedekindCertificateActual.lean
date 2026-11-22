import tmp.sheaf.xif.paper.S2216D5QuadraticTransportActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2487DedekindCertificateActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2216D5QuadraticTransportActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual

theorem S2487QuadraticIrreducible : S2167QuadraticIrreducible :=
  s2216_quadratic_irreducible

theorem S2487TenIrreducible : S2167TenIrreducible :=
  S2167TenIrreducible_proof

/-- With the Dedekind-Frobenius cycle comparison, the S2167 first missing is
closed. -/
theorem S2487FirstMissing_of_dedekind
    (h : DedekindFrobeniusCycleTypeTheorem) : S2167FirstMissing :=
  ⟨h, S2487QuadraticIrreducible⟩

/-- Exact remaining arithmetic input for the cycle-type route: the
Dedekind-Frobenius cycle comparison. -/
def S2487DedekindMissing : Prop := DedekindFrobeniusCycleTypeTheorem

/-- Exact linear-disjointness / Q-to-F' transport input, isolated in S2216. -/
def S2487TransportMissing : Prop := s2216LinearDisjointnessRequired

end LeanFormal.IUT.XiFPaper.S2487DedekindCertificateActual

end
