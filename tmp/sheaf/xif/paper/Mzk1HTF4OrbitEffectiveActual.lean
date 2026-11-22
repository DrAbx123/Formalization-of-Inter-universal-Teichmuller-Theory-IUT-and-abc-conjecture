import tmp.sheaf.xif.paper.Mzk1HTF4OrbitProductActual
import Mathlib.Tactic
/-!
# F4 geometric core: effectivity of the reduced zero divisor and of `F = divP − E`

Continues `Mzk1HTF4OrbitProductActual` (DONE 12:54:03): for `OrbitProductData`,
the reduced zero divisor `divP = ∑_{P(x)=0} [x]` is effective, `Ediv` is effective, and
`Fdiv = divP − Ediv` is effective whenever `E ⊆ {P = 0}` (the `hE_zero` field).
This supplies the `F ≥ 0` part of route §8.3's `div(P|_Y) = E + F`.

## Reuse / donor check (2026-11-17)
* `Mzk1HTF4OrbitProductActual` (DONE 12:54:03): `OrbitProductData`, `divP`, `Ediv`,
  `Fdiv`, `divP_eq_E_add_F`.
* ported `TauCeti/AlgebraicGeometry/WeilDivisor/Basic` (`coeff_sum_ofPoint`,
  `IsEffective`): olean available (probe 12:31:29).

**Explicit obligation**: the scheme-theoretic divisor with multiplicities/order of
vanishing and the Galois descent of the orbit products remain explicit (see the header
of `Mzk1HTF4OrbitProductActual`); this file only proves effectivity of the reduced model.
-/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4OrbitEffectiveActual
open LeanFormal.IUT.XiFPaper.HTF4OrbitProductActual
open TauCeti.AlgebraicGeometry

variable {ι X : Type*} [Fintype ι] [Fintype X] [DecidableEq X]

theorem Ediv_effective (D : OrbitProductData ι X) : WeilDivisor.IsEffective D.Ediv := by
  classical
  intro x
  have hE : D.Ediv.coeff x = (if x ∈ D.E then 1 else 0) := by
    simpa [OrbitProductData.Ediv] using (WeilDivisor.coeff_sum_ofPoint (s := D.E) x)
  rw [hE]
  split <;> norm_num

theorem divP_effective (D : OrbitProductData ι X) : WeilDivisor.IsEffective D.divP := by
  classical
  intro x
  have hdiv : D.divP.coeff x =
      (if MvPolynomial.eval (D.eval x) D.P = 0 then 1 else 0) := by
    simpa [OrbitProductData.divP] using
      (WeilDivisor.coeff_sum_ofPoint
        (s := Finset.univ.filter (fun y => MvPolynomial.eval (D.eval y) D.P = 0)) x)
  rw [hdiv]
  split <;> norm_num

theorem Fdiv_effective (D : OrbitProductData ι X) : WeilDivisor.IsEffective D.Fdiv := by
  classical
  intro x
  have hcoeff : WeilDivisor.coeff D.Fdiv x =
      WeilDivisor.coeff D.divP x - WeilDivisor.coeff D.Ediv x := by
    unfold OrbitProductData.Fdiv
    rw [WeilDivisor.coeff_sub]
  rw [hcoeff]
  have hdiv : D.divP.coeff x =
      (if MvPolynomial.eval (D.eval x) D.P = 0 then 1 else 0) := by
    simpa [OrbitProductData.divP] using
      (WeilDivisor.coeff_sum_ofPoint
        (s := Finset.univ.filter (fun y => MvPolynomial.eval (D.eval y) D.P = 0)) x)
  have hE : D.Ediv.coeff x = (if x ∈ D.E then 1 else 0) := by
    simpa [OrbitProductData.Ediv] using (WeilDivisor.coeff_sum_ofPoint (s := D.E) x)
  rw [hdiv, hE]
  by_cases hx : x ∈ D.E
  · have hx0 : MvPolynomial.eval (D.eval x) D.P = 0 := D.hE_zero x hx
    simp [hx, hx0]
  · split <;> norm_num

#print axioms Ediv_effective
#print axioms divP_effective
#print axioms Fdiv_effective
end LeanFormal.IUT.XiFPaper.HTF4OrbitEffectiveActual
end