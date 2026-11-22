import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

open CategoryTheory
open scoped TensorProduct

universe u

namespace S1747Probe

variable {K Bm Ai Aj : Type} [Field K] [Field Bm] [Field Ai] [Field Aj]
  [Algebra K Bm] [Algebra K Ai] [Algebra K Aj]
  (σi : Bm →ₐ[K] Ai) (σj : Bm →ₐ[K] Aj)

example : Algebra Bm Ai := σi.toRingHom.toAlgebra
example : Algebra Bm Aj := σj.toRingHom.toAlgebra

section
variable [Algebra Bm Ai] [Algebra Bm Aj]
  [IsScalarTower K Bm Ai] [IsScalarTower K Bm Aj]

example : CommRing (Ai ⊗[Bm] Aj) := inferInstance
example : CommSemiring (Ai ⊗[Bm] Aj) := inferInstance
example : Algebra K (Ai ⊗[Bm] Aj) := inferInstance
example : Algebra Ai (Ai ⊗[Bm] Aj) := inferInstance
example : Algebra Aj (Ai ⊗[Bm] Aj) := inferInstance

example (b : Bm) : (algebraMap Bm Ai b) ⊗ₜ[Bm] (1 : Aj) = (1 : Ai) ⊗ₜ[Bm] (algebraMap Bm Aj b) := by
  simp

end

section
-- now with the algebra instances induced by σ
set_option maxHeartbeats 400000 in
example : True := by
  letI : Algebra Bm Ai := σi.toRingHom.toAlgebra
  letI : Algebra Bm Aj := σj.toRingHom.toAlgebra
  haveI : IsScalarTower K Bm Ai := .of_algebraMap_eq fun k => by simp
  haveI : IsScalarTower K Bm Aj := .of_algebraMap_eq fun k => by simp
  have : CommRing (Ai ⊗[Bm] Aj) := inferInstance
  trivial

end

end S1747Probe
