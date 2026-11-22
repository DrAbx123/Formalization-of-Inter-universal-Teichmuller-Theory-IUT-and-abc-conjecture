import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
open Polynomial NumberField
namespace Probe2217
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]

example : Finite (RingOfIntegers K ⧸ p) := inferInstance
example : Fintype (RingOfIntegers K ⧸ p) := Fintype.ofFinite _

end
end Probe2217
