import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual

/-!
# A547 strict_measure instantiation and its named-input status

The `KummerXiERealization.strict_measure` field is not derivable from the
containment alone: a constant volume function on nonempty proper sets has
`qRegion ⊆ hullRegion` but no strict increase.  This file records the
counterexample and instantiates the realization from a minimal explicit volume
datum whose only substantive field is the strict increase.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312StrictMeasureInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Minimal explicit volume datum for the Kummer xi-e realization: monotone
volume, positive q volume, and the strict increase (the named non-vacuity input). -/
structure StrictHullVolume where
  vol : Set (S1902Carrier T) → Real
  vol_mono : ∀ {S U : Set (S1902Carrier T)}, S ⊆ U → vol S ≤ vol U
  q_pos : 0 < vol {qPilotInThetaCarrier T}
  strict_measure : vol {qPilotInThetaCarrier T} < vol (s1902Hull T)

/-- Instantiate the Kummer xi-e realization from the explicit volume datum. -/
noncomputable def kummerXiERealizationOfStrict (D : StrictHullVolume T) :
    KummerXiERealization T where
  vol := D.vol
  vol_mono := D.vol_mono
  q_pos := D.q_pos
  strict_measure := D.strict_measure

/-- The instantiated realization has the same strict measure witness. -/
theorem kummerXiERealizationOfStrict_strict (D : StrictHullVolume T) :
    (kummerXiERealizationOfStrict T D).vol {qPilotInThetaCarrier T} <
      (kummerXiERealizationOfStrict T D).vol (s1902Hull T) :=
  D.strict_measure

/-- The containment alone does NOT imply strict increase: the constant volume
`fun _ => 0` has no strict increase. -/
theorem constVolume_no_strict (S U : Set (S1902Carrier T)) :
    ¬ ((fun _ : Set (S1902Carrier T) => (0 : Real)) S <
        (fun _ : Set (S1902Carrier T) => (0 : Real)) U) :=
  lt_irrefl 0

end LeanFormal.IUT.XiFPaper.Mzk1Cor312StrictMeasureInstanceActual
