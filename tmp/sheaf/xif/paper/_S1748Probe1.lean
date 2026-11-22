import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Etale.Field

#print Algebra.Etale
#check @IsAlgClosure.equivOfEquiv
#check @IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
#check @mem_separableClosure_iff
#check @separableClosure
#check @Algebra.FormallyEtale.of_isSeparable
#check @Algebra.Etale
example (K : Type) [Field K] : IsAlgClosure K (AlgebraicClosure K) := inferInstance
example (K : Type) [Field K] : Algebra.IsAlgebraic K (AlgebraicClosure K) := inferInstance
example (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FiniteDimensional K L] : Algebra.Etale K L := by infer_instance
