import tmp.sheaf.xif.paper.Mzk1G1B1HPolyBranchSchemeActual
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Tactic

/-!
# B1 — the smooth ↔ derivative criterion `SmoothCriterion h` for the `t`-chart

Consumer: `Mzk1G1B1HPolySmoothLocusActual.hbridge_of_hcrit`, hence the `hbridge` lane
`Mzk1G1B1HPolyBranchSchemeActual` → `Mzk1G1HbObligationsActual` →
`Mzk1G1PhiFixedLBranchSupportActual`.

## Goal

`SmoothCriterion h := ∀ q : Spec ℚ[t], q ∈ (chartMorphismInf h).smoothLocus ↔ h' ∉ q`,
equivalently (`smoothCriterion_iff_ram`) `q ∈ Ram (chartMorphismInf h) ↔ h' ∈ q`.

## What is proved here (no sorry, no admit, no new axiom)

`evalAlg`: the `ℚ[λ]`-algebra structure on `ℚ[t]` with `algebraMap = evalAt h` (`λ ↦ h`),
with its API `evalAlg_algebraMap`, `evalAlg_algebraMap_apply`, `evalAlg_X`, `evalAlg_C`.
This is the ring-theoretic setting of the criterion: the criterion says that
`Spec.map (evalAt h)` is smooth at `q` exactly where `h' ∉ q` (`h' = derivative h`).

## Status of the two directions: not closed here; precise obstructions located

Both directions and the scheme ↔ ring bridge are recorded below as documentation only (no Lean
declaration asserts them, so nothing here is unproved).

* **Bridge** (`q ∈ smoothLocus (Spec.map (evalAt h)) ↔ ℚ[t]_q formally smooth over ℚ[λ]`).
  `Scheme.Hom.mem_smoothLocus` and `AlgebraicGeometry.Spec.localRingHom_comp_stalkIso`
  (`Mathlib/AlgebraicGeometry/Spec.lean`) express `(Spec.map f).stalkMap q` as
  `stalkIso⁻¹ ≫ ofHom (Localization.localRingHom (comap f q) q f rfl) ≫ stalkIso`; with
  `RingHom.FormallySmooth.respectsIso` and `Algebra.FormallySmooth.iff_restrictScalars`
  (localizations are formally étale, `Mathlib/RingTheory/Etale/Basic.lean`) this becomes the
  ring-level statement.  **Missing piece**: the `CommRingCat`-arrow-iso bookkeeping
  (`Arrow.mk _ ≅ Arrow.mk _` for `respectsIso`, plus unwrapping `Spec.map` through
  `Spec.toLocallyRingedSpace`) is packaged nowhere.
* **Direction B** (`h' ∉ q → smooth at q`), by infinitesimal lifting
  (`Algebra.FormallySmooth.of_comp_surjective`): lift `t` to `u₀ ∈ C` over a square-zero
  thickening `C → C ⧸ I`, then correct `u = u₀ + ε` with
  `ε = (y - h(u₀))·h'(u₀)⁻¹ ∈ I` where `y = algebraMap ℚ[λ] C λ`; Taylor in square-zero form
  (`Polynomial.aeval_add_of_sq_eq_zero`, `Mathlib/Algebra/Polynomial/Taylor.lean`) gives
  `h(u) = y`, so `evalAt u` is `ℚ[λ]`-linear, and `h' ∉ q` makes `h'(u)` a unit, allowing
  descent by `IsLocalization.lift` along `q.asIdeal.primeCompl`.  **Missing piece (the real
  obstruction)**: source and target of `evalAt h` are *the same type* `Polynomial ℚ`, so two
  algebra structures on that pair must coexist — `evalAlg h` and the *identity* structure used
  by `IsLocalization q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)`;
  `letI`-shadowing the former makes `algebraMap (Polynomial ℚ) (Localization.AtPrime q.asIdeal)`
  resolve to `λ ↦ h` and breaks the `IsLocalization` instance, while not shadowing it makes the
  lifting goal ill-typed (indeed the compatibility `IsScalarTower ℚ ℚ[λ] ℚ[t]` for `evalAlg`
  is not even synthesizable: `IsScalarTower.of_algebraMap_eq` is stuck on the pair of algebra
  structures).  Mathlib avoids this diamond exactly here:
  `Localization.AtPrime.algebraOfLiesOver` is deliberately not an instance ('to avoid diamonds
  in the situation where the top ring is already an algebra over
  `Localization.AtPrime p`').  A formalisation needs (a) an irreducible type synonym for
  `ℚ[λ]` with transport of the result, or (b) the presentation route over a renamed copy:
  `ℚ[λ][T,Z]/(λ - h(T), h'(T)·Z - 1)` is submersive (Jacobian `-h'(T)²`, a unit by the second
  relation) with `Algebra.IsStandardSmoothOfRelativeDimension 0`, hence `Algebra.Smooth`; the
  missing ingredient there is the graph isomorphism `ℚ[λ][T]/(λ - h(T)) ≅ ℚ[t]` (plus
  `Algebra.basicOpen_subset_smoothLocus_iff`, `Mathlib/RingTheory/Smooth/Locus.lean`).
* **Direction A** (`smooth at q → h' ∉ q`): `Algebra.IsSmoothAt.exists_notMem_smooth` gives
  `f ∉ q` with `Ω[ℚ[t]_f⁄ℚ[λ]]` free; `Ω[ℚ[t]⁄ℚ[λ]] ≅ ℚ[t]/(h')` (presentation `λ = h(T)`,
  `dλ = h'(T)dT`) localizes to `Ω ≅ ℚ[t]_f/(h')`, a nonzero torsion module over the domain
  `ℚ[t]_f` when `0 ≠ h' ∈ q`, hence not free — contradiction.  **Missing piece**: the Kähler
  computation `Ω[ℚ[t]⁄ℚ[λ]] ≅ ℚ[t]/(h')` (via
  `KaehlerDifferential.kerCotangentToTensor`) and its localization compatibility; the tree's
  `Mzk1G1OmegaActual.derivation_relation` /
  `Mzk1G1OmegaTransitionGlobalActual.overlap_derivation_relation` are the two-variable
  Fermat-chart relations, not this principal one.

## Consequence for the lane (why this is still the useful half)

Given the two directions and the bridge, `SmoothCriterion h` and the `hbridge` inclusion
`Ram (chartMorphismInf h) ⊆ derivativeZeroSet h` follow immediately; in particular **the lane
needs only direction B, not the full criterion**. See
`Mzk1G1B1HPolySmoothLocusActual.hbridge_of_smooth_criterion`, which takes exactly the
∀-pointwise form supplied by direction B plus the bridge.

No sorry, no admit, no new axioms.
-/
noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1SmoothCriterionActual

open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual

/-! ## The `ℚ[λ]`-algebra structure `λ ↦ h` on `ℚ[t]` -/

/-- The `ℚ[λ]`-algebra structure on `ℚ[t]` whose structure map is `evalAt h`, i.e. `λ ↦ h`.
(`ℚ[t]` already carries the *identity* algebra structure over itself, so this one has to be
written out explicitly and installed with `letI`; see the file header for the diamond this
causes in the pointwise smoothness statements.) -/
noncomputable def evalAlg (h : Polynomial ℚ) : Algebra (Polynomial ℚ) (Polynomial ℚ) :=
  (evalAt h).toAlgebra

theorem evalAlg_algebraMap (h : Polynomial ℚ) :
    @algebraMap (Polynomial ℚ) (Polynomial ℚ) _ _ (evalAlg h) = evalAt h :=
  RingHom.algebraMap_toAlgebra (evalAt h)

theorem evalAlg_algebraMap_apply (h : Polynomial ℚ) (p : Polynomial ℚ) :
    @algebraMap (Polynomial ℚ) (Polynomial ℚ) _ _ (evalAlg h) p = evalAt h p :=
  RingHom.congr_fun (evalAlg_algebraMap h) p

/-- The variable `λ` maps to `h`. -/
theorem evalAlg_X (h : Polynomial ℚ) :
    @algebraMap (Polynomial ℚ) (Polynomial ℚ) _ _ (evalAlg h) Polynomial.X = h := by
  rw [evalAlg_algebraMap_apply, evalAt_X]

/-- Constants are constants. -/
theorem evalAlg_C (h : Polynomial ℚ) (r : ℚ) :
    @algebraMap (Polynomial ℚ) (Polynomial ℚ) _ _ (evalAlg h) (Polynomial.C r) = Polynomial.C r := by
  rw [evalAlg_algebraMap_apply, evalAt_C, ← Polynomial.C_eq_algebraMap]

/-! ## Axiom checks -/

#print axioms evalAlg_algebraMap
#print axioms evalAlg_algebraMap_apply
#print axioms evalAlg_X
#print axioms evalAlg_C

end LeanFormal.IUT.XiFPaper.Mzk1G1B1SmoothCriterionActual
