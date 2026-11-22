import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.GroupTheory.Torsion
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup

noncomputable section
open scoped WithZero
open ValuativeRel

namespace S2049Probe

#check ProfiniteGrp.ProfiniteCompletion.completion
#check ProfiniteGrp.ProfiniteCompletion.eta
#check ProfiniteGrp.ProfiniteCompletion.etaFn
#check ProfiniteGrp.ProfiniteCompletion.denseRange
#check GrpCat.of
#check Multiplicative

abbrev Zhat : Type := ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))

example : Group Zhat := inferInstance
example : TopologicalSpace Zhat := inferInstance
example : CompactSpace Zhat := inferInstance
example : TotallyDisconnectedSpace Zhat := inferInstance

def zhatOfInt : Multiplicative ℤ →* Zhat :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (Multiplicative ℤ))).hom

#check ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of (Multiplicative ℤ))

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

#check IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
#check ValuativeRel.valuation K
#check WithZero.unitsWithZeroEquiv
#check Units.map

noncomputable def normalizedValuation : Kˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    ((Units.map (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidWithZeroHom.toMonoidHom).comp
      (Units.map (ValuativeRel.valuation K).toMonoidWithZeroHom.toMonoidHom))

#check normalizedValuation K

variable {L : Type*} [Field L] [Algebra K L]
#check Gal(L/K)
#check IntermediateField
#check AlgebraicClosure K
#check IntermediateField.fixedField
#check Subgroup.zpowersHom
#check zpowersHom

end S2049Probe
