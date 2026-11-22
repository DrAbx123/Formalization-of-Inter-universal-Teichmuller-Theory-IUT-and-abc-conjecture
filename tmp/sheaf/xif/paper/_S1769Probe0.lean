import Mathlib.RingTheory.Etale.Finite
import Mathlib.FieldTheory.AbsoluteGaloisGroup

open CategoryTheory CategoryTheory.Limits

noncomputable section
universe u

variable (K : Type u) [Field K] (Omega : Type u) [Field Omega] [Algebra K Omega]

example : Module.Free K Omega := inferInstance
example : Module.FaithfullyFlat K Omega := inferInstance
example : IsSepClosed (AlgebraicClosure K) := inferInstance
