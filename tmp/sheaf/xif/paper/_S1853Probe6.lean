import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section
open scoped TensorProduct

example (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] : Module.FaithfullyFlat k Ω := inferInstance

example (k : Type*) [Field k] : Module.FaithfullyFlat k (AlgebraicClosure k) := inferInstance

#synth Module.Free k (AlgebraicClosure k)

