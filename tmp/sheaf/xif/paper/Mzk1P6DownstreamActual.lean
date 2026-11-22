/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P6KviPlaceActual
import tmp.sheaf.xif.paper.Mzk1P6PacketConsumerActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6DownstreamActual
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
variable {l : PrimeGeFive} (X : N8NativeInput l)
theorem p6_kviPlace_same_source_consumer :
    comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) = nativeBadBasePlace X :=
  nativeFPlaceOverBad_comap X
theorem p6_kviPlace_mem_bad_consumer :
    comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) ∈ X.S.tuple.source.V_mod_bad :=
  nativeFPlaceOverBad_mem_bad X
#print axioms p6_kviPlace_same_source_consumer
#print axioms p6_kviPlace_mem_bad_consumer
end LeanFormal.IUT.XiFPaper.Mzk1P6DownstreamActual
