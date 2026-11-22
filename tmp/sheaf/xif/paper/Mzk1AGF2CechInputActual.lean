import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_AdelicIndex
import Mathlib.Tactic
/-!
# F2.1 Čech input → ported `RiemannGenusReachedAt`

Route §4.2 item 7: on the actual plane model `Y_n` use
`0 → O_{P²}(m−n) → O_{P²}(m) → i_* O_Y(m) → 0`; the Laurent-monomial Čech
computation on the standard affine cover gives `H¹(Y, O_Y(m)) = 0` for `m ≥ n−2`
(and the Hilbert-function difference).  Transferring a concrete large divisor `mH` gives
`RiemannGenusReachedAt γ D₀` with `γ = (n−1)(n−2)/2`.

This file records the **wiring**: once the Čech computation supplies
(i) `FiniteDimensional K (LSpace D₀)`, (ii) the index equality at `D₀`,
(iii) the maximality bound `∀ D, deg D − ell D ≤ γ−1`, the ported
`AlgebraicCurve.RiemannGenusReachedAt` is obtained.  The three analytic/Čech facts are
**explicit fields** (`F2CechData`) and are NOT proved here: the Laurent-monomial
Čech computation is the remaining obligation (see below).

## Reuse / donor check (2026-11-17)
* ported `tmp/external/ported/flt_core/Definitions/Def_AlgebraicCurve_AdelicIndex.lean`
  (`RiemannGenusReachedAt`, `LSpace`, `ell`, `Divisor.degree`) — olean available;
* ported `S_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge` (`eq_of_ge_port`) — olean
  available, consumes `RiemannGenusReachedAt` downstream;
* `AG12CechRiemannRochActual.ag12_cechRiemannRoch` (DONE consumer, conditional on
  `RiemannGenusReachedAt`).

**Explicit obligations (not proved here)**
1. the standard affine cover `S₀,S₁` of `Y_n` and the Laurent-monomial Čech complex;
2. `H¹` vanishing for `O_Y(m)`, `m ≥ n−2` (the combinatorial monomial computation);
3. the Hilbert function difference / degree-ell index equality at the concrete `D₀ = mH`;
4. maximality `∀ D, deg D − ell D ≤ γ−1` (follows from RR + vanishing).
Owner: andrew (Čech), with alan (F2.1 residue/different) and grace (RR existence).
F2.1 is **not closed** by this file.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.AGF2CechInputActual
open AlgebraicCurve
universe u

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- The three Čech/RR facts needed for `RiemannGenusReachedAt`, as explicit data. -/
structure F2CechData (γ : ℤ) (D₀ : Divisor K F) where
  finite : FiniteDimensional K (LSpace D₀)
  eq : Divisor.degree D₀ - (ell D₀ : ℤ) = γ - 1
  isMax : ∀ D : Divisor K F, Divisor.degree D - (ell D : ℤ) ≤ γ - 1

/-- Wiring: Čech data ⇒ ported `RiemannGenusReachedAt`. -/
theorem riemannGenusReachedAt_of_cech {γ : ℤ} {D₀ : Divisor K F}
    (D : F2CechData (K := K) (F := F) γ D₀) : RiemannGenusReachedAt γ D₀ :=
  ⟨D.finite, D.eq, D.isMax⟩

/-- Downstream consumer: the ported Čech Riemann-Roch package (`AG12`) is now applicable
once the two-chart cover data is supplied. -/
theorem cechData_has_genusReached {γ : ℤ} {D₀ : Divisor K F}
    (D : F2CechData (K := K) (F := F) γ D₀) : Nonempty (RiemannGenusReachedAt γ D₀) :=
  ⟨riemannGenusReachedAt_of_cech D⟩

#print axioms riemannGenusReachedAt_of_cech
#print axioms cechData_has_genusReached
end LeanFormal.IUT.XiFPaper.AGF2CechInputActual
end