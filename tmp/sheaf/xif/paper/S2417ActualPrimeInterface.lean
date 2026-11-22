import tmp.sheaf.xif.paper.S2280PaperVPrimeMatchActual

/-! # S2417: actual-prime O^× interface at qVFamTensorP

S2268 gives an unconditional integral-units/O^×μ equivalence at the actual
prime `s2268p = qVFamTensorP` of `sectionKPlace T b`.  This file packages that
interface, carrying the equality `prime = qVFamTensorP`, and checks the 3.12
Kummer-arrow consumer.  The unit interface itself does not need
`qVFamTensorP ≤ 7`; however the actual Kummer arrow is indexed by
`LocV = FinitePrimePlace 2 7`, so consuming it at `qVFamTensorP` requires a
paper place `v` with `v.1 = qVFamTensorP`, which is exactly S2135. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2417ActualPrimeInterface

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2268LocalBridgeActual
open LeanFormal.IUT.XiFPaper.S2280PaperVPrimeMatchActual
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2034OperationKummerActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def s2417OUnitsAtSectionKPlace :
    S2219PaperOUnits T b ≃* LocalOFieldUnits (s2268p T b) :=
  s2268IntegralUnitsEquiv T b

noncomputable def s2417OUnitsMuAtSectionKPlace :
    S2219PaperOUnitsMu T b ≃*
      TimesMuQuotient (LocalOFieldUnits (s2268p T b)) :=
  s2268MuEquiv T b

/-- The actual-prime unit interface.  The prime is the actual `s2268p`, with
its unconditional identification with `qVFamTensorP`. -/
structure S2417ActualPrimeOUnits
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  prime : Nat
  prime_eq : prime = qVFamTensorP T b
  [primeFact : Fact (Nat.Prime prime)]
  OUnitsEquiv : S2219PaperOUnits T b ≃* LocalOFieldUnits prime
  OUnitsMuEquiv : S2219PaperOUnitsMu T b ≃*
    TimesMuQuotient (LocalOFieldUnits prime)

noncomputable def s2417ActualPrimeOUnits :
    S2417ActualPrimeOUnits T b where
  prime := s2268p T b
  prime_eq := s2280_sectionKPlace_prime_eq_qVFamTensorP T b
  primeFact := s2268pFact T b
  OUnitsEquiv := s2417OUnitsAtSectionKPlace T b
  OUnitsMuEquiv := s2417OUnitsMuAtSectionKPlace T b

/-- A 3.12 Kummer-arrow index at qVFamTensorP, i.e. a paper place v with that
rational prime. -/
def S2417KummerPrimeIndexRequired : Prop :=
  ∃ v : LocV, v.1 = qVFamTensorP T b

/-- The Kummer index exists exactly when S2135 holds. -/
theorem s2417KummerPrimeIndex_iff_S2135 :
    S2417KummerPrimeIndexRequired T b ↔
      S2135PrimeAlignmentRequired T b := by
  constructor
  · rintro ⟨v, hv⟩
    change qVFamTensorP T b ∈ primeStrip 2 7
    rw [← hv]
    exact v.2
  · intro h
    exact ⟨⟨qVFamTensorP T b, h⟩, rfl⟩

/-- Given a Kummer index, the actual S2268 local bridge transports
`actualOUnitsMu v` to the sectionKPlace prime unit quotient. -/
noncomputable def s2417KummerBridgeOfIndex
    (v : LocV) (hv : v.1 = qVFamTensorP T b) :
    actualOUnitsMu v ≃*
      TimesMuQuotient (LocalOFieldUnits (s2268p T b)) :=
  (s2268LocalBridge T b v
    (hv.trans (s2280_sectionKPlace_prime_eq_qVFamTensorP T b).symm)).trans
    (s2417OUnitsMuAtSectionKPlace T b)

/-- Consumer audit: the unit interface is unconditional, while the actual
Kummer arrow is consumable exactly under the S2135 index condition. -/
theorem s2417KummerConsumerAudit :
    Nonempty (S2417ActualPrimeOUnits T b) ∧
      (S2417KummerPrimeIndexRequired T b ↔
        S2135PrimeAlignmentRequired T b) ∧
      (∀ (v : LocV) (hv : v.1 = qVFamTensorP T b),
        Nonempty (actualOUnitsMu v ≃*
          TimesMuQuotient (LocalOFieldUnits (s2268p T b)))) := ⟨
  ⟨s2417ActualPrimeOUnits T b⟩,
  s2417KummerPrimeIndex_iff_S2135 T b,
  fun v hv => ⟨s2417KummerBridgeOfIndex T b v hv⟩⟩

#check s2417OUnitsAtSectionKPlace
#check s2417OUnitsMuAtSectionKPlace
#check S2417ActualPrimeOUnits
#check s2417ActualPrimeOUnits
#check S2417KummerPrimeIndexRequired
#check s2417KummerPrimeIndex_iff_S2135
#check s2417KummerBridgeOfIndex
#check s2417KummerConsumerAudit

end LeanFormal.IUT.XiFPaper.S2417ActualPrimeInterface
end
