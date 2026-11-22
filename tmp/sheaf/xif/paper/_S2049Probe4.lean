import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.GroupTheory.Torsion
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup

noncomputable section
open scoped WithZero
open ValuativeRel

namespace S2049Probe4

abbrev Zhat : Type := ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))

def zhatOfInt : Multiplicative ℤ →* Zhat :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (Multiplicative ℤ))).hom

theorem denseRange_zhatOfInt : DenseRange zhatOfInt :=
  ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of (Multiplicative ℤ))

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

noncomputable def normalizedValuation : Kˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    ((Units.map (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidWithZeroHom.toMonoidHom).comp
      (Units.map (ValuativeRel.valuation K).toMonoidWithZeroHom.toMonoidHom))

structure UnramifiedGaloisData (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] where
  Lur : IntermediateField K (AlgebraicClosure K)
  galEquiv : Gal(Lur/K) ≃ₜ* Zhat

namespace UnramifiedGaloisData

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (d : UnramifiedGaloisData K)

noncomputable def frobenius : Gal(d.Lur/K) :=
  d.galEquiv.symm (zhatOfInt (Multiplicative.ofAdd 1))

noncomputable def artin : Kˣ →* Gal(d.Lur/K) :=
  d.galEquiv.symm.toMonoidHom.comp (zhatOfInt.comp (normalizedValuation K))

#check ContinuousMulEquiv.apply_symm_apply
#check MulEquiv.apply_symm_apply

theorem galEquiv_artin (x : Kˣ) :
    d.galEquiv (d.artin x) = zhatOfInt (normalizedValuation K x) := by
  change d.galEquiv (d.galEquiv.symm (zhatOfInt (normalizedValuation K x))) = _
  rw [ContinuousMulEquiv.apply_symm_apply]

end UnramifiedGaloisData

end S2049Probe4
