import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Category.CommAlgCat.Basic

open CategoryTheory CategoryTheory.Limits

universe u

namespace S1771

variable {K : Type u} [Field K]

-- type checks
#check (fun (B : Type u) [CommRing B] (I : Ideal B) => (I : Submodule B B))
#check (fun (B : Type u) [CommRing B] (I J : Ideal B) => (I ⊓ J : Ideal B))
#check (fun (B : Type u) [CommRing B] (I J : Ideal B) => (show Submodule B B from I))

end S1771
