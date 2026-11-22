import tmp.sheaf.xif.paper.S2132FrobCycleActual
import Mathlib.RingTheory.Frobenius

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Polynomial
open NumberField

namespace LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

noncomputable def rootPerm
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (f : (RingOfIntegers K)[X])
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (sigma : Gal(L/K)) :
    Equiv.Perm ((f.map (algebraMap (RingOfIntegers K) K)).rootSet L) :=
  let p : K[X] := f.map (algebraMap (RingOfIntegers K) K)
  have hmap : p.map (algebraMap K L) = f.map (algebraMap (RingOfIntegers K) L) := by
    simp [p, Polynomial.map_map, IsScalarTower.algebraMap_eq]
  have h : (p.map (algebraMap K L)).Splits := by
    rw [hmap]
    exact hsplit
  letI : Fact ((p.map (algebraMap K L)).Splits) := ⟨h⟩
  MulAction.toPermHom (Gal(L/K)) (p.rootSet L) sigma

noncomputable def rootCycleType
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (f : (RingOfIntegers K)[X])
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (sigma : Gal(L/K)) : Multiset Nat :=
  letI := Classical.decEq ((f.map (algebraMap (RingOfIntegers K) K)).rootSet L)
  (rootPerm K L f hsplit sigma).cycleType

end LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
end
