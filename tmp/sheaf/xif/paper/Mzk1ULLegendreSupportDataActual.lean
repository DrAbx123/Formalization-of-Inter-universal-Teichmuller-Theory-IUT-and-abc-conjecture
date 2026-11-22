/- U-C: instantiate david's LegendreSupportIncl with the discriminant prime support.

Reuse: `Mzk1ULHcondChainActual.LegendreSupportIncl`/`tpd_subset_point_of` (david,
00:48:16) + our `Mzk1ULLegendreDiscSupportActual.legendre_disc_primeFactors_subset`
(12:28:47).  The q-support and the point-bad primes are taken to be the {lam,lam-1}
prime support; the tripodal bad primes the discriminant prime support, which is
contained in it up to {2} by the discriminant lemma.
-/
import tmp.sheaf.xif.paper.Mzk1ULLegendreDiscSupportActual
import tmp.sheaf.xif.paper.Mzk1ULHcondChainActual
import Mathlib.Tactic

namespace LeanFormal.IUT.XiFPaper.Mzk1ULLegendreSupportDataActual

open LeanFormal.IUT.XiFPaper.Mzk1ULLegendreDiscSupportActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHcondChainActual

/-- the Legendre support-inclusion data, built from the discriminant prime support
(tpdBadPrimes = prime factors of 16 lam^2 (lam-1)^2, qSupport = pointBadPrimes =
prime factors of lam and lam-1, as in the paper's Legendre bad-prime analysis). -/
noncomputable def legendreSupportIncl (lam : ℕ) (h2 : 2 ≤ lam) : LegendreSupportIncl where
  qSupport := lam.primeFactors ∪ (lam - 1).primeFactors
  tpdBadPrimes := (16 * lam ^ 2 * (lam - 1) ^ 2).primeFactors
  pointBadPrimes := lam.primeFactors ∪ (lam - 1).primeFactors
  tpd_subset := by
    intro p hp
    have h := legendre_disc_primeFactors_subset lam h2 hp
    -- h : p in lam.pf ∪ (lam-1).pf ∪ {2}; goal: p in (lam.pf ∪ (lam-1).pf) ∪ {2}
    simpa [Finset.union_assoc] using h
  q_subset_point := by
    intro p hp
    exact Finset.mem_union.mpr (Or.inl hp)

/-- PROVED: the Legendre tripodal bad primes sit in the point bad primes up to {2}. -/
theorem legendre_tpd_subset_point (lam : ℕ) (h2 : 2 ≤ lam) :
    (legendreSupportIncl lam h2).tpdBadPrimes ⊆ (legendreSupportIncl lam h2).pointBadPrimes ∪ {2} :=
  tpd_subset_point_of (legendreSupportIncl lam h2)

end LeanFormal.IUT.XiFPaper.Mzk1ULLegendreSupportDataActual