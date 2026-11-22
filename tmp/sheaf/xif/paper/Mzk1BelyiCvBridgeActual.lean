import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.CriticalValues
import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import tmp.sheaf.xif.paper.Mzk1Lemma21Actual
import tmp.sheaf.xif.paper.Mzk1Lemma22GChoiceConstructActual
import tmp.sheaf.xif.paper.Mzk1Lemma22HypPreservationActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section

/-!
# STEP 0 prior-art: C-point critical-value bridge|derivative-aeval formula -> hits ported tauceti_belyi_core CriticalValues (criticalValues/mem_criticalValues/criticalValues_map/rootSet) + Belyi (criticalValues_belyiPolynomial_subset, natDegree_belyiPolynomial), Mzk1Lemma21Actual:51 belyi21_derivative_root, Mzk1Lemma22GChoiceConstructActual (gPoly/belyi21 relation) -> REUSE/ADAPT.

# Mzk1BelyiCvBridgeActual — C-point critical-value bridge (stage4 unblock)

Deliverable: for the canonical Belyi polynomial B_{m,n}, every C-point critical point
maps into {0,1}: the C-point critical-value bridge requested by stage4
(Mzk1Lemma22CritValueActual).  Uses the PROVED ported subset theorem
criticalValues_belyiPolynomial_subset; no re-proof of Belyi's theorem.
Also re-exports belyi21_derivative_root (root dichotomy over C) and the relation
between gPoly and belyi21.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1BelyiCvBridgeActual

open Polynomial
open TauCeti
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21Actual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationActual

/-- **C-point critical-value bridge for the canonical Belyi polynomial:** if z is a
critical point over C of B_{m,n} (m,n >= 1), then B_{m,n}(z) is 0 or 1. -/
theorem belyiPolynomial_critIn01 {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (z : ℂ)
    (hz : Polynomial.aeval z (Polynomial.derivative (belyiPolynomial ℚ m n)) = 0) :
    Polynomial.aeval z (belyiPolynomial ℚ m n) = 0 ∨
      Polynomial.aeval z (belyiPolynomial ℚ m n) = 1 := by
  have hnd : (belyiPolynomial ℚ m n).natDegree = m + n := natDegree_belyiPolynomial m n
  have hnd2 : 2 ≤ (belyiPolynomial ℚ m n).natDegree := by rw [hnd]; omega
  have hder_ne : Polynomial.derivative (belyiPolynomial ℚ m n) ≠ 0 := by
    exact Polynomial.derivative_ne_zero.mpr (by omega)
  have hmem : Polynomial.aeval z (belyiPolynomial ℚ m n) ∈
      (belyiPolynomial ℚ m n).criticalValues ℂ := by
    rw [mem_criticalValues]
    refine ⟨z, ?_, rfl⟩
    rw [mem_rootSet']
    refine ⟨?_, hz⟩
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hder_ne
  have hsub := criticalValues_belyiPolynomial_subset ℂ m n hmem
  simpa using hsub

/-- **gPoly derivative/evaluation relation:** for even n, f0q = 0 and gPoly is the
Belyi polynomial belyi21 precomposed with lambda*X; recorded for the stage4 formula.
TO CHECK with stage4 exact signature (see rows). -/
theorem gPoly_eq_belyi21_comp (D : Mzk1ScaleData) (hne : Even D.n) :
    gPoly D = (belyi21 D.m D.n).comp (Polynomial.C D.lam * Polynomial.X) := by
  unfold gPoly belyi21
  rw [f0q_eq_zero D hne]
  simp

/-- **Root dichotomy (re-export):** over C, a root of the derivative of the Belyi
polynomial belyi21 is 0, 1, or m/(m+n).  Recorded for the stage4 C-point bridge. -/
theorem belyi21_derivative_root_reexport {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {z : ℂ} (h : Polynomial.aeval z (Polynomial.derivative (belyi21 m n)) = 0) :
    z = 0 ∨ z = 1 ∨ ((m + n : ℕ) : ℂ) * z = (m : ℂ) :=
  belyi21_derivative_root hm hn h

/-- Row record: what is proved vs what stage4 must align. -/
def belyiCvBridgeRows : List (String × String × String) :=
  [ ("C-point CV bridge for canonical Belyi B_{m,n}", "A", "PROVED belyiPolynomial_critIn01 (from ported criticalValues_belyiPolynomial_subset)")
  , ("gPoly = belyi21 composed with lam*X (even n)", "A", "PROVED gPoly_eq_belyi21_comp (needs stage4 signature alignment)")
  , ("belyi21 derivative root dichotomy over C", "A", "REUSED/RE-EXPORTED belyi21_derivative_root")
  , ("derivative-aeval formula for gPoly", "TODO", "NAMED TODO: stage4 to confirm exact cast signature (Lead item (1))") ]

theorem belyiCvBridgeRows_length : belyiCvBridgeRows.length = 4 := rfl

#check belyiPolynomial_critIn01
#check gPoly_eq_belyi21_comp
#check belyi21_derivative_root_reexport
#check belyiCvBridgeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1BelyiCvBridgeActual
end