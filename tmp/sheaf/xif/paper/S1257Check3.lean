import Mathlib
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
#check AlgEquiv.toAlgHom
#check AlgEquiv.toRingEquiv
#check AlgEquiv.symm
#check RingEquiv.toMonoidHom
#check Units.map
