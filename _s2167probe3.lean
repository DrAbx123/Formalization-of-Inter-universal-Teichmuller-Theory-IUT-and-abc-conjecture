import Mathlib

open Polynomial
open NumberField

noncomputable section

namespace S2167Probe

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

-- generic action from action on L
example : MulSemiringAction Gal(L/K) (𝓞 L) := inferInstance

example : SMulCommClass Gal(L/K) (𝓞 K) L := inferInstance

example : SMulCommClass Gal(L/K) (𝓞 K) (𝓞 L) := inferInstance

end S2167Probe
