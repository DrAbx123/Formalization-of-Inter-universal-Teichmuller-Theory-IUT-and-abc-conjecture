import tmp.sheaf.xif.paper.S2417ActualPrimeInterface
import tmp.sheaf.xif.paper.S2404QPilotArithmeticActual
import tmp.sheaf.xif.paper.S2362MainlineReadoutActual
import tmp.sheaf.xif.paper.S2391QMarkReadoutActual
import tmp.sheaf.xif.paper.S2396SourceReadoutAuditActual
import tmp.sheaf.xif.paper.S2373C1ReadoutActual

/-! # S2422: actual-prime Kummer interface and C1-to-hull mainline

(A) The actual unit quotient at `s2268p = qVFamTensorP` is unconditional.
The actual Kummer arrow is indexed by `LocV = FinitePrimePlace 2 7`; a Kummer
index at the actual prime exists exactly under S2135.  This file packages both
the unconditional unit interface and the conditional Kummer consumption.

(C) The S2404 q-pilot arithmetic identity feeds the S2391/S2396/S2373/S2362
chain, giving `Q_C ≤ signedHullLogVolume` and hull finiteness. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2422MainlineC9Actual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2268LocalBridgeActual
open LeanFormal.IUT.XiFPaper.S2280PaperVPrimeMatchActual
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2034OperationKummerActual
open LeanFormal.IUT.XiFPaper.S2417ActualPrimeInterface
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2404QPilotArithmeticActual
open LeanFormal.IUT.XiFPaper.S2391QMarkReadoutActual
open LeanFormal.IUT.XiFPaper.S2396SourceReadoutAuditActual
open LeanFormal.IUT.XiFPaper.S2373C1ReadoutActual
open LeanFormal.IUT.XiFPaper.S2362MainlineReadoutActual
open OriginalInput
open SourceHodgeTheaterBridge

universe u v w uv upi umon ui ux uy

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{u, uv, upi, umon, ui} l V}
variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
variable {P : H2SpokePermutation I}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable [Fintype Label]
variable {W : SourceInternalWiring I R P X Y}
variable {S : SourceP1P2Input (I := I) (R := R) (P := P)
  (X := X) (Y := Y) W}
variable {B : SourceP1P2Bundle W S}

/-! ## A. Actual-prime unit/Kummer interface -/

/-- Unconditional actual unit quotient at the qVFam prime. -/
structure S2422UnitInterface
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  actualPrime : Nat
  prime_eq : actualPrime = qVFamTensorP T b
  [primeFact : Fact (Nat.Prime actualPrime)]
  unitQuotient : S2219PaperOUnitsMu T b ≃*
    TimesMuQuotient (LocalOFieldUnits actualPrime)

noncomputable def s2422UnitInterface :
    S2422UnitInterface T b where
  actualPrime := s2268p T b
  prime_eq := s2280_sectionKPlace_prime_eq_qVFamTensorP T b
  primeFact := s2268pFact T b
  unitQuotient := s2417OUnitsMuAtSectionKPlace T b

/-- Conditional actual Kummer consumption at that prime: the actual Kummer
arrow index `v : LocV` with `v.1 = qVFamTensorP`. -/
structure S2422KummerConsumptionAtPrime
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  unitInterface : S2422UnitInterface T b
  index : LocV
  index_eq : index.1 = unitInterface.actualPrime

/-- The Kummer index condition is exactly S2135. -/
theorem s2422KummerIndex_iff_S2135 :
    (∃ v : LocV, v.1 = qVFamTensorP T b) ↔
      S2135PrimeAlignmentRequired T b :=
  s2417KummerPrimeIndex_iff_S2135 T b

/-! ## C. C1 projection to the signed hull -/

/-- The S2404 arithmetic identity gives the S2391/S2396 source readout equal to
the actual profile readout. -/
theorem s2422_profile_eq_source
    (b : BridgeOutput (B := B) (R := R))
    (E : S2404QPilotArithmeticRequired b) :
    R.input.profile.logVolume b.out.source =
      sourceQPilotSignedLog I.initial := by
  exact (s2404_candidate_eq_out b).symm.trans E.arithmetic_identity.symm

/-- C1 projection from the q-pilot arithmetic identity. -/
noncomputable def s2422C1ProjectionOfArithmetic
    {Xh : Type ux} {p : PaperSignedHull Xh Label}
    {F : S2362FixedCData p}
    (b : BridgeOutput (B := B) (R := R))
    (E : S2404QPilotArithmeticRequired b)
    (hQ : F.qPilotLogVolume = sourceQPilotSignedLog I.initial) :
    S2362C1OutputReadoutProjectionRequired p F :=
  s2373Projection b
    (s2391QMarkReadoutEqOfSourceEq b (s2422_profile_eq_source b E)) hQ

/-- The full scalar mainline: from the paper-level arithmetic identity, the
C1 projection gives `Q_C ≤ signedHullLogVolume` and finite hull volume. -/
theorem s2422_qPilot_le_hull_of_arithmetic
    {Xh : Type ux} {p : PaperSignedHull Xh Label}
    {F : S2362FixedCData p}
    (b : BridgeOutput (B := B) (R := R))
    (E : S2404QPilotArithmeticRequired b)
    (hQ : F.qPilotLogVolume = sourceQPilotSignedLog I.initial) :
    (s2362ReadoutOfProjection
        (s2422C1ProjectionOfArithmetic b E hQ)).Q_C ≤
      p.signedHullLogVolume ∧
    p.ambient.logVolume p.ambient.hull < ⊤ :=
  s2362_mainline_scalar_of_projection
    (s2422C1ProjectionOfArithmetic b E hQ)

#check S2422UnitInterface
#check s2422UnitInterface
#check S2422KummerConsumptionAtPrime
#check s2422KummerIndex_iff_S2135
#check s2422_profile_eq_source
#check s2422C1ProjectionOfArithmetic
#check s2422_qPilot_le_hull_of_arithmetic

end LeanFormal.IUT.XiFPaper.S2422MainlineC9Actual
end
