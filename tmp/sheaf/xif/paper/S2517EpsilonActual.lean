import tmp.sheaf.xif.paper.S2511InfinityPointUB
import tmp.sheaf.xif.paper.S2512StackOpenImmersionUB
import tmp.sheaf.xif.paper.S2513SeparationUB

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S2508CuspDataUB
open LeanFormal.IUT.XiFPaper.S2511InfinityPointUB
open LeanFormal.IUT.XiFPaper.S2512StackOpenImmersionUB
open LeanFormal.IUT.XiFPaper.S2513SeparationUB
noncomputable local instance : Field UB := inferInstance
noncomputable local instance : CommRing UB := inferInstance
noncomputable local instance : Field S2490A.K := S2490A.fieldK
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2517EpsilonActual

/-- The full cusp datum: infinity point + separation + stack open immersion. -/
noncomputable def S2517CuspDatum : S2508CuspDatum :=
  S2512CuspDatumOf S2511Point S2513Separation

/-- The actual epsilon: the boundary cusp of S2495cK. -/
noncomputable def S2517Epsilon :=
  S2508CuspDatum.boundaryCusp S2517CuspDatum

#check S2517Epsilon
#print axioms S2517Epsilon
end LeanFormal.IUT.XiFPaper.S2517EpsilonActual
end