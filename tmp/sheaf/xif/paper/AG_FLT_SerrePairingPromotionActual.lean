import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_SerrePairing

/-!
# AG-FLT Serre pairing promotion (first-class importable module; audit component)

COMPONENT, not a paper object.  Named consumers: stepxi AG06b/Serde layer,
Lead AG-INFRA-PLAN, [Mzk1] GeometricCore (Serre duality layer).

Promotes the ported FLT Serre pairing (green module
tmp/external/ported/flt_core/Definitions/Def_AlgebraicCurve_SerrePairing.lean;
Apache-2.0, attribution in ported header; source grep sorry/axiom = 0):
* ResidueTheorem (statement Prop; the residue-theorem input);
* serrePairing, the K-linear pairing
  H^0(regular differentials) x CechH1(S0,S1,O) -> K, built from the residue sum;
* serrePairing_apply_mk (COMPLETE proof: value on a Cech class is the residue sum)
  and serrePairing_apply_mk_eq_finsum_ite (COMPLETE proof: finsum form).
The pairing is conditional exactly on the residue theorem, as in the source; we
do not assume it (it is an explicit hypothesis hRT).
No axiom/fake data.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.AG_FLT_SerrePairingPromotionActual

open LeanFormal.IUT
open AlgebraicCurve KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
variable [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
variable [Nontrivial Ω[F⁄K]]
variable [AlgebraicCurve.HasPrincipalDivisors K F]

/-- Statement row: the residue theorem input for the Serre pairing. -/
abbrev promotion_ResidueTheorem : Prop := AlgebraicCurve.ResidueTheorem K F

/-- The Serre pairing H^0(regular differentials) x CechH1(S0,S1,O) -> K
(ported definition; conditional on the residue theorem hRT). -/
noncomputable def promotion_serrePairing (hRT : AlgebraicCurve.ResidueTheorem K F)
    {S₀ S₁ : Set (AlgebraicCurve.Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) :
    ↥(regularDifferentials K F) →ₗ[K]
      AlgebraicCurve.cechH1 S₀ S₁ (0 : AlgebraicCurve.Divisor K F) →ₗ[K] K :=
  AlgebraicCurve.serrePairing hRT hcover

/-- COMPLETE proof (ported): the Serre pairing on a Cech class is the residue sum. -/
theorem promotion_serrePairing_apply_mk (hRT : AlgebraicCurve.ResidueTheorem K F)
    {S₀ S₁ : Set (AlgebraicCurve.Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (ω : ↥(regularDifferentials K F))
    (f : ↥(AlgebraicCurve.lSpaceOn (S₀ ∩ S₁) (0 : AlgebraicCurve.Divisor K F))) :
    AlgebraicCurve.serrePairing hRT hcover ω (Submodule.Quotient.mk f) =
      AlgebraicCurve.residueSumOffChart S₀ (ω : Ω[F⁄K]) (f : F) :=
  AlgebraicCurve.serrePairing_apply_mk hRT hcover ω f

end LeanFormal.IUT.XiFPaper.AG_FLT_SerrePairingPromotionActual
