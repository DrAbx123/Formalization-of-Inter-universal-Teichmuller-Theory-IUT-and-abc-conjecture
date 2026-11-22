import Mathlib.RingTheory.Etale.Finite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.RingTheory.Etale.Field

open CategoryTheory

universe u

variable (K : Type u) [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω]

example (L : IntermediateField K Ω) [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Finite K L := inferInstance
example (L : IntermediateField K Ω) [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Algebra.Etale K L := by infer_instance

#check @FintypeCat.equivEquivIso
#check @FintypeCat.homMk
#check @MulEquiv.ofBijective
#check @AlgEquiv.ofRingEquiv
#check @IntermediateField.mem_adjoin_simple_self
#check @IntermediateField.adjoin.finiteDimensional
#check @isSeparable_adjoin_simple_iff_isSeparable
#check @IntermediateField.inclusion
#check @Algebra.FormallyEtale.equivPiOfIsSepClosed
#check @Polynomial.Separable
#check @IsSeparable
#check @isSeparable_iff_minpoly
