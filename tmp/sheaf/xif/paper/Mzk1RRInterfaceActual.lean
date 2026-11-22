import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_IsCurveOver
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_AdelicIndex
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_RiemannRochRows
import tmp.external.ported.flt_core.Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import tmp.external.ported.flt_core.Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed
import tmp.external.ported.flt_core.P2M.Sol.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed

/-!
# Mzk1RRInterfaceActual — RR interface exported on the flt_core types

STEP 0 prior-art: the self-contained flt_core port (Apache-2.0, commit 6e837e75) of the
function-field Riemann–Roch chain is complete and compiled (5-file serial EXIT=0 today);
this file imports ONLY the flt_core root (no flt_th, no flt_test, hence no duplicate
AlgebraicCurve.Divisor definitions) and exports the interface the D GeometricCore route
needs, every item annotated with its flt_core source and olean status:

(i)  functionFieldRiemannRoch_interface : AlgebraicCurve.FunctionFieldRiemannRoch K F
     (real ported proof; axioms = propext, Classical.choice, Quot.sound only);
(ii) ell_eq_zero_of_degree_neg_interface
     (flt_core Theorems/Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg.lean);
(iii) degree_canonicalDivisor_interface : degree (canonicalDivisorOf hω) = 2 * genus - 2
     (derived from the flt_core chain's p0n25_wkc_degree_canonicalDivisor_eq_of_weilMax and
     p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax, both proved inside
     S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean);
(iv) basic divisor facts for the pencil/zero-divisor route:
     degree_single_interface, deg_eq_one_interface, punctureDivisor + degree_punctureDivisor
     (defined/proved here on the flt_core types).
No new axioms, no placeholders; the remaining named inputs of (iii) are the exact
weil-maximality/constants hypotheses of the ported theorem. Registry frozen 14041.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual

open AlgebraicCurve

universe u v

/-- (i) Function-field Riemann–Roch, PROVED from the ported flt_core chain. -/
theorem functionFieldRiemannRoch_interface
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F] :
    AlgebraicCurve.FunctionFieldRiemannRoch K F :=
  AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed

/-- (ii) Ell vanishes on negative-degree divisors (flt_core proof). -/
theorem ell_eq_zero_of_degree_neg_interface {K F : Type*} [Field K] [Field F] [Algebra K F]
    {D : AlgebraicCurve.Divisor K F} [AlgebraicCurve.IsCurveOver K F]
    (hD : AlgebraicCurve.Divisor.degree D < 0) :
    AlgebraicCurve.ell D = 0 :=
  AlgebraicCurve.ell_eq_zero_of_degree_neg hD

/-- (iii) degree of a canonical divisor is 2g-2, derived from the ported chain's
canonical-divisor degree theorem plus its Stichtenoth-genus = genus identification. -/
theorem degree_canonicalDivisor_interface
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.IsCurveOver K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ (v : AlgebraicCurve.Place K F), v.DCoordGenerates]
    [Nonempty (AlgebraicCurve.Place K F)]
    [FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F))]
    {γ : ℤ} {D₀ : AlgebraicCurve.Divisor K F}
    (h : AlgebraicCurve.RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (AlgebraicCurve.adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ AlgebraicCurve.omegaSpace (AlgebraicCurve.canonicalDivisorOf hω) ∧
      ∀ D : AlgebraicCurve.Divisor K F,
        φ ∈ AlgebraicCurve.omegaSpace D → D ≤ AlgebraicCurve.canonicalDivisorOf hω)
    (hC : AlgebraicCurve.ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    AlgebraicCurve.Divisor.degree (AlgebraicCurve.canonicalDivisorOf hω)
      = 2 * (AlgebraicCurve.genus K F : ℤ) - 2 := by
  have hγ : γ = (AlgebraicCurve.genus K F : ℤ) :=
    P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.ModularCurve.p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax
      h hsup hC
  have hdeg :=
    P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.ModularCurve.p0n25_wkc_degree_canonicalDivisor_eq_of_weilMax
      h hsup hC hω
  rw [hdeg, hγ]

/-- (iv-a) Degree of a single divisor. -/
theorem degree_single_interface {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) (n : ℤ) :
    AlgebraicCurve.Divisor.degree (Finsupp.single v n) = n * v.deg :=
  AlgebraicCurve.Divisor.degree_single v n

/-- (iv-b) Over an algebraically closed base every place has degree one. -/
theorem deg_eq_one_interface {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [AlgebraicCurve.IsCurveOver K F] (v : AlgebraicCurve.Place K F) :
    v.deg = 1 :=
  AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed v

namespace Curve

/-- (iv-c) The puncture divisor of a finite place set (flt_core types). -/
def punctureDivisor {K F : Type*} [Field K] [Field F] [Algebra K F]
    (T : Finset (AlgebraicCurve.Place K F)) : AlgebraicCurve.Divisor K F :=
  ∑ t ∈ T, Finsupp.single t (1 : ℤ)

/-- (iv-c) Degree of the puncture divisor is the cardinality (algebraically closed base). -/
theorem degree_punctureDivisor {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [AlgebraicCurve.IsCurveOver K F]
    (T : Finset (AlgebraicCurve.Place K F)) :
    AlgebraicCurve.Divisor.degree (punctureDivisor T) = (T.card : ℤ) := by
  classical
  rw [punctureDivisor, map_sum]
  have h : ∀ t ∈ T,
      AlgebraicCurve.Divisor.degree (Finsupp.single t (1 : ℤ)) = 1 := by
    intro t _
    rw [AlgebraicCurve.Divisor.degree_single,
      AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed t]
    norm_num
  rw [Finset.sum_congr rfl h]
  simp

end Curve

/-- Interface rows: (item, flt_core source file, olean status / evidence). -/
def rrInterfaceRows : List (String × String × String) :=
  [ ("(i) FunctionFieldRiemannRoch", "Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean + P2M/Sol/S_..._of_isAlgClosed.lean", "REAL PROOF re-exported; olean present; serial EXIT=0; axioms trio only"),
    ("(ii) ell_eq_zero_of_degree_neg", "Theorems/Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg.lean", "olean present; re-exported"),
    ("(iii) degree canonical divisor = 2g-2", "P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean:6113+6132 (ModularCurve.p0n25_wkc_degree_canonicalDivisor_eq_of_weilMax / p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax)", "olean present; derived corollary compiled here (weil-max/constants hypotheses explicit)"),
    ("(iv) degree_single", "Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:192", "olean present; re-exported"),
    ("(iv) deg_eq_one_of_isAlgClosed", "Definitions/Def_AlgebraicCurve_IsCurveOver.lean:68", "olean present; re-exported"),
    ("(iv) punctureDivisor + degree = |T|", "built here on flt_core types (same shape as Mzk1GeomCorePencilActual but flt_core-root native)", "PROVED here"),
    ("ell (adelic index)", "Definitions/Def_AlgebraicCurve_AdelicIndex.lean:19 (abbrev ell = finrank K (LSpace D))", "olean present; available for consumers") ]

/-- The interface row record has seven rows. -/
theorem rrInterfaceRows_length : rrInterfaceRows.length = 7 := rfl

#check functionFieldRiemannRoch_interface
#check ell_eq_zero_of_degree_neg_interface
#check degree_canonicalDivisor_interface
#check degree_single_interface
#check deg_eq_one_interface
#check Curve.degree_punctureDivisor
#check rrInterfaceRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual
end
