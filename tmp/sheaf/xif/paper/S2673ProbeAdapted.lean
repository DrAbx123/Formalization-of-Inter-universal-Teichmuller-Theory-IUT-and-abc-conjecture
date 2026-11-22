import tmp.sheaf.xif.paper.S2577Away10FbarActual
import tmp.sheaf.xif.paper.S2663P10PrimeActual
import tmp.sheaf.xif.paper.S2532LocalizedDefinitionsActual
import tmp.sheaf.xif.paper.S2548ConcreteCycleTypeActual

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2577Away10FbarActual

namespace LeanFormal.IUT.XiFPaper.S2673ProbeAdapted

abbrev R10 : Type := S2537ConcreteLocalizationActual.R
abbrev T10 : Type := S2537ConcreteLocalizationActual.S
abbrev OL : Type := S2537ConcreteLocalizationActual.C
abbrev K : Type := S2537ConcreteLocalizationActual.K
abbrev L10 : Type := S2537ConcreteLocalizationActual.L

#check (inferInstance : IsFractionRing R10 K)
#check (inferInstance : IsFractionRing OL L10)
#check (inferInstance : IsFractionRing T10 L10)
#check (inferInstance : IsDedekindDomain R10)
#check (inferInstance : IsIntegrallyClosed R10)
#check (inferInstance : FiniteDimensional K L10)
#check (inferInstance : IsGalois K L10)
#check (inferInstance : Finite (Gal(L10/K)))
#check (inferInstance : Module.Finite ℤ OL)
#check (inferInstance : Algebra.IsIntegral R10 T10)
#check (inferInstance : FaithfulSMul R10 T10)
#check (inferInstance : MulSemiringAction Gal(L10/K) L10)
#check (inferInstance : SMulCommClass Gal(L10/K) K L10)
#check (inferInstance : NumberField K)
#check (inferInstance : NumberField L10)
#check (inferInstance : Ring.HasFiniteQuotients OL)

end LeanFormal.IUT.XiFPaper.S2673ProbeAdapted
end
