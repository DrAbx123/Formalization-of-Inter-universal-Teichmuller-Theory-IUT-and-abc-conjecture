/- A3 / F2.1 item 2: abstract construction of a canonical divisor from a generator differential.

  RECON (per Lead): `HasCanonicalDivisor` has NO producer anywhere in the tree
  (grep over flt_core / flt_test / AG*; only the class and its consumers). The class is
  `∀ ω ≠ 0, ∃ D : Place →₀ ℤ, ∀ v, D v = v.ordDifferential ω`. The abstract reduction below
  shows that it suffices to have ONE nonzero differential `ω₀` which generates `Ω[F⁄K]` as an
  F-module (`hgen`) and whose order function has finite support (`hfin`): then any `ω` is
  `c • ω₀`, and `ordDifferential (c • ω₀) = ord c + ordDifferential ω₀`
  (`Place.ordDifferential_smul`), with both terms finitely supported
  (`HasPrincipalDivisors.exists_divisor` for the function `c`).

  For the Fermat curve the remaining (concrete, item1-dependent) inputs are: a nonzero global
  differential `ω₀` (A4's `Mzk1G1OmegaActual.omegaForm`, Ω free rank one via
  `Mzk1G1OmegaFreeActual`), the spanning property (Ω is F-rank one over the function field),
  and the finite-support statement (ω₀ is a unit multiple of the local generator at all but
  finitely many places -- on chart-0 it is a basis, so the support lies over `x = 0`, finitely
  many points). These are registered as the remaining wiring after item 1 (function field and
  places). No sorry/axiom. -/
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import tmp.external.ported.flt_core.Definitions.Def_ModularCurve_CanonicalDivisor
import Mathlib.Tactic

noncomputable section
open AlgebraicCurve KaehlerDifferential
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2CanonicalDivisorActual

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial (KaehlerDifferential K F)]
  [HasPrincipalDivisors K F]

/-- **抽象 canonical divisor 构造**：若 `ω₀ ≠ 0` 生成 `Ω[F⁄K]`（作为 F-模）且其 ord 函数
    有限支撑，则 `HasCanonicalDivisor K F`。 -/
theorem hasCanonicalDivisor_of_isGenerator {ω₀ : KaehlerDifferential K F} (hω₀ : ω₀ ≠ 0)
    (hgen : ∀ ω : KaehlerDifferential K F, ∃ c : F, ω = c • ω₀)
    (hfin : {v : Place K F | v.ordDifferential ω₀ ≠ 0}.Finite) :
    HasCanonicalDivisor (K := K) (F := F) := by
  classical
  refine ⟨fun ω hω => ?_⟩
  obtain ⟨c, hcω⟩ := hgen ω
  have hc : c ≠ 0 := by
    intro h
    rw [hcω, h, zero_smul] at hω
    exact hω rfl
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) c hc
  let F0 : Place K F →₀ ℤ :=
    Finsupp.onFinset hfin.toFinset (fun v => v.ordDifferential ω₀) (by
      intro v hv
      simpa using hv)
  refine ⟨D + F0, fun v => ?_⟩
  rw [Finsupp.add_apply, hD v, Finsupp.onFinset_apply, hcω]
  exact (Place.ordDifferential_smul c ω₀).symm

#print axioms hasCanonicalDivisor_of_isGenerator

end LeanFormal.IUT.XiFPaper.Mzk1G1F2CanonicalDivisorActual