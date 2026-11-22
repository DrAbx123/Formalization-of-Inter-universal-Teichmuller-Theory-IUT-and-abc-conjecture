import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1AnnulusMeasureActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # Resolved acceptance: positive actual annulus resolves strict_measure -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceResolvedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasureActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual annulus data for the resolved acceptance: q singleton inside the hull,
positive q measure, positive annulus measure, and additivity of the volume. -/
noncomputable def actualAnnulusData (vol : Set (S1902Carrier T) → Real)
    (q_pos : 0 < vol {qPilotInThetaCarrier T})
    (annulus_pos : 0 < vol (s1902Hull T \ {qPilotInThetaCarrier T})) :
    XiEAnnulusData (α := S1902Carrier T) (vol := vol) where
  qRegion := {qPilotInThetaCarrier T}
  hullRegion := s1902Hull T
  subset := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact qPilotInThetaCarrier_mem_hull T
  q_pos := q_pos
  annulus_pos := annulus_pos

/-- The resolved realization of the genuine Kummer xi-e data: strict_measure is
derived from the positive actual annulus, not supplied as a named field. -/
noncomputable def realizationOfActualAnnulus (vol : Set (S1902Carrier T) → Real)
    (vol_mono : forall {S U : Set (S1902Carrier T)}, S ⊆ U -> vol S ≤ vol U)
    (q_pos : 0 < vol {qPilotInThetaCarrier T})
    (annulus_pos : 0 < vol (s1902Hull T \ {qPilotInThetaCarrier T}))
    (hadd : forall s t : Set (S1902Carrier T), Disjoint s t -> vol (s ∪ t) = vol s + vol t) :
    KummerXiERealization T where
  vol := vol
  vol_mono := vol_mono
  q_pos := q_pos
  strict_measure :=
    strictMeasure_of_annulus (actualAnnulusData T vol q_pos annulus_pos) hadd

/-- The paper reading built from the resolved realization. -/
noncomputable def readingOfActualAnnulus (vol : Set (S1902Carrier T) → Real)
    (vol_mono : forall {S U : Set (S1902Carrier T)}, S ⊆ U -> vol S ≤ vol U)
    (q_pos : 0 < vol {qPilotInThetaCarrier T})
    (annulus_pos : 0 < vol (s1902Hull T \ {qPilotInThetaCarrier T}))
    (hadd : forall s t : Set (S1902Carrier T), Disjoint s t -> vol (s ∪ t) = vol s + vol t) :
    PaperKummerReading T where
  D := realizationOfActualAnnulus T vol vol_mono q_pos annulus_pos hadd
  qReading := Real.log (vol {qPilotInThetaCarrier T})
  thetaReading := Real.log (vol (s1902Hull T))
  qReading_log := rfl
  thetaReading_log := rfl

/-- Signed q reading of the resolved realization is the log of the q volume. -/
theorem readingSignedQ_eq (vol : Set (S1902Carrier T) → Real)
    (vol_mono : forall {S U : Set (S1902Carrier T)}, S ⊆ U -> vol S ≤ vol U)
    (q_pos : 0 < vol {qPilotInThetaCarrier T})
    (annulus_pos : 0 < vol (s1902Hull T \ {qPilotInThetaCarrier T}))
    (hadd : forall s t : Set (S1902Carrier T), Disjoint s t -> vol (s ∪ t) = vol s + vol t) :
    requirementSignedQ (requirementOfReading T
        (readingOfActualAnnulus T vol vol_mono q_pos annulus_pos hadd)) =
      Real.log (vol {qPilotInThetaCarrier T}) := rfl

/-- **Resolved acceptance**: final conclusion with strict_measure derived from the
positive actual annulus (no named strict_measure input). -/
theorem cor312Conclusion_resolved (vol : Set (S1902Carrier T) → Real)
    (vol_mono : forall {S U : Set (S1902Carrier T)}, S ⊆ U -> vol S ≤ vol U)
    (q_pos : 0 < vol {qPilotInThetaCarrier T})
    (annulus_pos : 0 < vol (s1902Hull T \ {qPilotInThetaCarrier T}))
    (hadd : forall s t : Set (S1902Carrier T), Disjoint s t -> vol (s ∪ t) = vol s + vol t)
    (hqneg : requirementSignedQ (requirementOfReading T
      (readingOfActualAnnulus T vol vol_mono q_pos annulus_pos hadd)) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T
        (readingOfActualAnnulus T vol vol_mono q_pos annulus_pos hadd) hqneg
        ipl hipl she hshe apt hapt) :=
  cor312Conclusion_final T
    (readingOfActualAnnulus T vol vol_mono q_pos annulus_pos hadd) hqneg
    ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceResolvedActual
