import tmp.sheaf.xif.paper.S2132FrobCycleActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Polynomial
open NumberField

namespace LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

example (K L : Type) [Field K] [Field L] [Algebra K L] (f : (RingOfIntegers K)[X]) :
    f.map ((algebraMap K L).comp (algebraMap (RingOfIntegers K) K)) =
      f.map (algebraMap (RingOfIntegers K) L) := by
  rw [show (algebraMap K L).comp (algebraMap (RingOfIntegers K) K) =
      algebraMap (RingOfIntegers K) L from IsScalarTower.algebraMap_eq (RingOfIntegers K) K L]

end LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
end
