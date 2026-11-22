import tmp.sheaf.xif.paper.Mzk1RRInterfaceActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreRRProvedActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: D-RR canonical-degree strengthening -> Mzk1RRInterfaceActual.degree_canonicalDivisor_interface (flt_core chain: canonical degree = 2g-2, with named weil-max/ConstantsAreBase hypotheses) + Mzk1GeomCoreRRProvedActual.punctureDivisor/degree_punctureDivisor + flt_core ell_eq_zero_of_degree_neg -> PROVED hdual from the EXACT 2g-2 degree; named inputs explicit (no closure).

# Mzk1GeomCoreRRCanonicalDegreeActual — canonical degree 2g-2 and hdual discharge

PROVED:
* `canonical_degree_eq_two_genus_sub_two`: degree K = 2g-2 (re-export of the interface
  theorem; consumes named RiemannGenusReachedAt/weil-max/ConstantsAreBase inputs);
* `hdual_of_canonical_degree`: the two dual-vanishing terms of the pencil route vanish,
  now from the EXACT degree 2g-2 (stronger than the 2g-1 bound used in
  Mzk1GeomCoreRRProvedActual).
NAMED: the three interfaced hypotheses of the canonical-degree theorem.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRCanonicalDegreeActual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRProvedActual

universe u v

/-- **PROVED:** canonical divisor degree is exactly 2g-2 (interface theorem re-export). -/
theorem canonical_degree_eq_two_genus_sub_two {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalLocalResidueKStar K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ (v : Place K F), v.DCoordGenerates]
    [Nonempty (Place K F)]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2 :=
  degree_canonicalDivisor_interface h hsup hC hω

/-- **PROVED:** the pencil dual-vanishing terms follow from the exact canonical degree. -/
theorem hdual_of_canonical_degree {K F : Type*} [Field K] [IsAlgClosed K] [Infinite K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    (hdeg : Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2)
    (T : Finset (Place K F)) (hcard : 2 * (genus K F : ℤ) + 1 ≤ (T.card : ℤ)) :
    (∀ t ∈ T,
      (ell (canonicalDivisorOf hω - punctureDivisor T) : ℤ) = 0 ∧
      (ell (canonicalDivisorOf hω - (punctureDivisor T - Finsupp.single t (1 : ℤ))) : ℤ) = 0) := by
  intro t ht
  have hdegT : Divisor.degree (punctureDivisor T) = (T.card : ℤ) :=
    degree_punctureDivisor T
  have hlt1 : Divisor.degree (canonicalDivisorOf hω - punctureDivisor T) < 0 := by
    rw [map_sub, hdegT, hdeg]
    linarith
  have hdegsub : Divisor.degree (punctureDivisor T - Finsupp.single t (1 : ℤ))
      = (T.card : ℤ) - 1 := by
    rw [map_sub, hdegT, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed t]
    norm_num
  have hlt2 : Divisor.degree
      (canonicalDivisorOf hω - (punctureDivisor T - Finsupp.single t (1 : ℤ))) < 0 := by
    rw [map_sub, hdegsub, hdeg]
    linarith
  exact ⟨by simpa using (ell_eq_zero_of_degree_neg_interface hlt1),
    by simpa using (ell_eq_zero_of_degree_neg_interface hlt2)⟩

/-- Rows: proved canonical-degree strengthening vs named interface hypotheses. -/
def canonicalDegreeRows : List (String × String × String) :=
  [ ("canonical degree = 2g-2", "PROVED (re-export)", "canonical_degree_eq_two_genus_sub_two / flt_core chain p0n25_wkc_degree_canonicalDivisor")
  , ("dual vanishing from exact 2g-2", "PROVED", "hdual_of_canonical_degree (stronger than the 2g-1 bound route)")
  , ("RiemannGenusReachedAt / weil-max / ConstantsAreBase", "NAMED (interfaced)", "explicit hypotheses of degree_canonicalDivisor_interface")
  , ("zero divisor existence", "PROVED elsewhere", "Mzk1GeomCoreRRProvedActual.zero_divisor_exists_proved (uses 2g-1 bound; no named inputs)") ]

theorem canonicalDegreeRows_length : canonicalDegreeRows.length = 4 := rfl

#check canonical_degree_eq_two_genus_sub_two
#check hdual_of_canonical_degree
#check canonicalDegreeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRCanonicalDegreeActual
end