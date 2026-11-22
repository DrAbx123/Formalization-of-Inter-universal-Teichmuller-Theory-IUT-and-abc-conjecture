import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

noncomputable section
open ValuativeRel

namespace S2049Probe5

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- A candidate maximal-unramified predicate: the fixed field of the inertia
subgroup of a valuation subring extending the valuation ring of L. -/
def IsMaximalUnramified (Lur : IntermediateField L (AlgebraicClosure L)) : Prop :=
  ∃ A : ValuationSubring (AlgebraicClosure L),
    (∀ x : L, algebraMap L (AlgebraicClosure L) x ∈ A ↔
      ValuativeRel.valuation L x ≤ 1) ∧
    Lur = IntermediateField.fixedField
      ((A.inertiaSubgroup L).map (A.decompositionSubgroup L).subtype)

structure UnramifiedGaloisData where
  Lur : IntermediateField L (AlgebraicClosure L)
  isMaximalUnramified : IsMaximalUnramified L Lur
  galEquiv : Gal(Lur/L) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))

end S2049Probe5
