import tmp.sheaf.xif.paper.GlobalRealifiedFrobenioidActual
import tmp.sheaf.xif.paper.GlobalFrobenioidPresentationActual
import tmp.sheaf.xif.paper.S3133QPilotPaperMissingActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual

namespace LeanFormal.IUT.XiFPaper.Mzk1FrobenioidPresentationConstructionActual

/-- Exact investigation of the N5 gap 5: the realified global Frobenioid
presentation.  Documentation only; no fake inhabitant. -/
def Mzk1FrobenioidPresentationMissingFields : List String :=
  [ "available actual object layer: GlobalRealifiedFrobenioidCarrier (GlobalRealifiedFrobenioidActual) with baseCategory = GlobalBaseCategory (SingleObj Unit), primeIndex = NumberFieldPlace Fmod, divisorMonoid = Multiplicative (Finsupp places Real), valueFunctor, degree, realification, unit, primeObject; globalRealifiedFrobenioidCarrier is constructed",
    "available actual presentation: GlobalFrobenioidPresentationActual.globalFrobenioidPresentationActual (K := Fmod) = numberFieldFrobenioidPresentation Fmod, an actual Iut.FrobenioidPresentation for the number-field model Frobenioid of Fmod (baseCategory/carrier/preFrobenioid/divisorMonoid/structureFunctor/axioms/connectedness/totalEpimorphic all actual fields)",
    "missing field 1: an Iut.FrobenioidPresentation whose base/carrier categories are those of the realified global object C^boxplus_mod, not the Example36 number-field model; the existing numberFieldFrobenioidPresentation has a different base category and divisor monoid",
    "missing field 2: concrete identification of the presentation's preFrobenioid.divisorMonoid (a DivisorialMonoidOn BottomBase BottomFSM) with GlobalDivisorMonoid X = Multiplicative (GlobalPrimeIndex ->0 Real); this type identification and its monoid/DivisorialMonoidOn structure are absent",
    "missing field 3: concrete identification of the presentation's degree/realification with globalDegree X : GlobalDivisorMonoid -> Multiplicative Real (and globalDegreeFun), including compatibility with the divisor monoid identification",
    "missing field 4: the q_v family and the global q object as an object of the presentation: an embedding/identification of qPilotRealifiedDivisor X (S3133) and the qV zero-locus divisors into the presentation carrier/divisor monoid, with the realification and degree readouts matching qPilotRealifiedLogVolume",
    "missing field 5: FrobenioidAxioms, carrierConnected, baseConnected, carrierTotallyEpimorphic, baseTotallyEpimorphic for the realified global presentation; the number-field model presentation supplies them only for its own carrier",
    "the existing MissingRealifiedGlobalFrobenioidPresentation structure has three fields realified_divisorMonoid_identification / realified_degree_identification / qPilotRealification_identification of bare type Prop: inhabiting them by True would be vacuous/fake, and no concrete proposition is currently defined; they must be replaced by the concrete identifications above",
    "qVFam/global q data alone (qVFamily, qPilotRealifiedDivisor, qPilotRealifiedLogVolume) provide divisor/volume objects but no category, structure functor, or FrobenioidAxioms; they cannot construct FrobenioidPresentation without the categorical fields above",
    "no fake, no True/PUnit/axiom/sorry; this file records the exact missing fields and the actual available object layer" ]

