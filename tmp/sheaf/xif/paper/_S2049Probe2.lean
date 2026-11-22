import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.GroupTheory.Torsion
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup

noncomputable section
open scoped WithZero
open ValuativeRel

namespace S2049Probe2

abbrev Zhat : Type := ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))

def zhatOfInt : Multiplicative ℤ →* Zhat :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (Multiplicative ℤ))).hom

theorem denseRange_zhatOfInt : DenseRange (zhatOfInt) :=
  ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of (Multiplicative ℤ))

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

noncomputable def normalizedValuation : Kˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    ((Units.map (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidWithZeroHom.toMonoidHom).comp
      (Units.map (ValuativeRel.valuation K).toMonoidWithZeroHom.toMonoidHom))

theorem normalizedValuation_eq_one_iff (u : Kˣ) :
    normalizedValuation K u = 1 ↔ ValuativeRel.valuation K (u : K) = 1 := by
  let valueGroupValue : (ValueGroupWithZero K)ˣ :=
    Units.map (ValuativeRel.valuation K).toMonoidWithZeroHom.toMonoidHom u
  let integerValue : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidWithZeroHom.toMonoidHom
      valueGroupValue
  change WithZero.unitsWithZeroEquiv integerValue = 1 ↔ _
  constructor
  · intro h
    have integerValue_eq_one : integerValue = 1 :=
      WithZero.unitsWithZeroEquiv.injective (by simpa only [map_one] using h)
    have valueGroupValue_eq_one : valueGroupValue = 1 := by
      apply (Units.map_injective
        (f := (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidWithZeroHom.toMonoidHom)
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective)
      simpa only [integerValue, map_one] using integerValue_eq_one
    exact congrArg Units.val valueGroupValue_eq_one
  · intro h
    have valueGroupValue_eq_one : valueGroupValue = 1 := Units.ext h
    have integerValue_eq_one : integerValue = 1 := by
      change Units.map _ valueGroupValue = 1
      rw [valueGroupValue_eq_one, map_one]
    simpa only [map_one] using congrArg WithZero.unitsWithZeroEquiv integerValue_eq_one

/-- The exact P1 carrier interface: the maximal unramified extension together with
its Galois group identified with the profinite integers. -/
structure UnramifiedGaloisData (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] where
  Lur : IntermediateField K (AlgebraicClosure K)
  galEquiv : Gal(Lur/K) ≃* Zhat

namespace UnramifiedGaloisData

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (d : UnramifiedGaloisData K)

noncomputable def frobenius : Gal(d.Lur/K) := d.galEquiv.symm 1

noncomputable def artin : Kˣ →* Gal(d.Lur/K) :=
  d.galEquiv.symm.toMonoidHom.comp (zhatOfInt.comp (normalizedValuation K))

theorem galEquiv_artin (x : Kˣ) :
    d.galEquiv (d.artin x) = zhatOfInt (normalizedValuation K x) := by
  simp [artin]

theorem artin_unit {u : Kˣ} (hu : ValuativeRel.valuation K (u : K) = 1) :
    d.artin u = 1 := by
  apply d.galEquiv.injective
  rw [galEquiv_artin, (normalizedValuation_eq_one_iff K u).mpr hu, map_one, map_one]

end UnramifiedGaloisData

end S2049Probe2
