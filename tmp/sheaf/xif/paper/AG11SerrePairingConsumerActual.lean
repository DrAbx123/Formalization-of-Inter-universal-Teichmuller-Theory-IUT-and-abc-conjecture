import tmp.sheaf.xif.paper.AG_FLT_SerrePairingPromotionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# AG11: Serre pairing / Serre-duality layer consumer (A-class reuse)

Consumes qpilot's canonical Serre-pairing promotion
(AG_FLT_SerrePairingPromotionActual, checker CITABLE 2):
* promotion_ResidueTheorem : Prop — statement row (residue-theorem input);
* promotion_serrePairing : the K-linear pairing
  H^0(regular differentials) x CechH1(S0,S1,O) -> K, conditional on hRT exactly as in
  the source;
* promotion_serrePairing_apply_mk : COMPLETE proof (value on a Cech class = residue
  sum; ported, no sorry).
Together with AG05 (Cech H0/H1), AG10 (canonical divisor/genus) and AG06b (RR rows +
complete reductions), this completes the A-class Serre-duality layer of the bottom-up
AG chain toward [Mzk1] GeometricCore.  The residue theorem is an explicit hypothesis
(class B paper row), NOT assumed.

NOTE: this file imports ONLY the ported flt_core Serre module; it does not import
adapted-module promotions in the same file (avoids flt/adapted duplicate-namespace
clash).

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG11SerrePairingConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.AG_FLT_SerrePairingPromotionActual
open AlgebraicCurve KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
variable [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
variable [Nontrivial Ω[F⁄K]]
variable [AlgebraicCurve.HasPrincipalDivisors K F]

/-- The residue theorem statement row (class B paper input; NOT assumed). -/
abbrev ag11ResidueTheorem : Prop := AlgebraicCurve.ResidueTheorem K F

/-- The Serre pairing H^0(regular differentials) x CechH1(S0,S1,O) -> K (A-class
reuse of the ported construction; conditional on hRT exactly as in the source). -/
noncomputable def ag11SerrePairing (hRT : AlgebraicCurve.ResidueTheorem K F)
    {S₀ S₁ : Set (AlgebraicCurve.Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) :
    ↥(regularDifferentials K F) →ₗ[K]
      AlgebraicCurve.cechH1 S₀ S₁ (0 : AlgebraicCurve.Divisor K F) →ₗ[K] K :=
  promotion_serrePairing (K := K) (F := F) hRT hcover

/-- Value formula: the pairing on a Cech class is the residue sum (COMPLETE ported
proof; A-class). -/
theorem ag11SerrePairing_apply_mk (hRT : AlgebraicCurve.ResidueTheorem K F)
    {S₀ S₁ : Set (AlgebraicCurve.Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (ω : ↥(regularDifferentials K F))
    (f : ↥(AlgebraicCurve.lSpaceOn (S₀ ∩ S₁) (0 : AlgebraicCurve.Divisor K F))) :
    AlgebraicCurve.serrePairing hRT hcover ω (Submodule.Quotient.mk f) =
      AlgebraicCurve.residueSumOffChart S₀ (ω : Ω[F⁄K]) (f : F) :=
  promotion_serrePairing_apply_mk (K := K) (F := F) hRT hcover ω f

/-- A-class reuse record. -/
def ag11SerdeReuse : List (String × String × String) :=
  [ ("Serre pairing H0(regular differentials) x CechH1 -> K", "AG_FLT_SerrePairingPromotionActual (CITABLE 2; ported flt_core)", "A (pairing + value formula COMPLETE; conditional on hRT)"),
    ("residue theorem", "promotion_ResidueTheorem (statement row)", "class B paper row; explicit hypothesis"),
    ("Serre duality / RR rows", "AG_FLT_RiemannRochPromotionActual (separate canonical module; not imported here to avoid namespace clash)", "A (reuse in its own consumers)"),
    ("Cech H0/H1", "AG05CechActual (CechPromotion, adapted)", "A (reuse)") ]

end LeanFormal.IUT.XiFPaper.AG11SerrePairingConsumerActual

end
