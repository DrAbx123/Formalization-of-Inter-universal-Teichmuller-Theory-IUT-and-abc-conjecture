import tmp.sheaf.xif.paper.S2725ThetaImageHullActual
import tmp.sheaf.xif.paper.GlobalPositiveThetaHullLogVolumeActual
import tmp.sheaf.xif.paper.S2730PointScalingComparisonActual

noncomputable section
open scoped BigOperators Pointwise
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalPositiveThetaHullLogVolumeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2731PointScaledHullActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : forall v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

abbrev S2731Carrier : Type uv := (v : V) -> I.ThetaPilotPoint v

def S2731UnitRegion : Set (S2731Carrier (I := I) (V := V)) :=
  Set.pi Set.univ (fun v => ({1} : Set (I.ThetaPilotPoint v)))

def S2731PointScale
    (point x : S2731Carrier (I := I) (V := V)) :
    S2731Carrier (I := I) (V := V) :=
  fun v => point v * x v

def S2731PointScaledRegion
    (point : S2731Carrier (I := I) (V := V)) :
    Set (S2731Carrier (I := I) (V := V)) :=
  S2731PointScale (I := I) point '' S2731UnitRegion (I := I) (V := V)

def S2731Hull : Set (S2731Carrier (I := I) (V := V)) :=
  Set.pi Set.univ (fun v => (I.sourceHolomorphicHull v (R v) n : Set (I.ThetaPilotPoint v)))

def S2731Image : Set (S2731Carrier (I := I) (V := V)) :=
  Set.pi Set.univ (fun v => I.possibleThetaPilotImageSet v (R v) n)

noncomputable def S2731HullLogVolume : Real :=
  globalThetaHullPositiveLogVolume (I := I) R n

theorem S2731Image_subset_hull :
    S2731Image (I := I) R n <= S2731Hull (I := I) R n := by
  intro x hx
  rw [S2731Image, Set.mem_pi] at hx
  rw [S2731Hull, Set.mem_pi]
  intro v _
  exact I.possibleThetaPilotImage_subset_sourceHolomorphicHull v (R v) n (hx v trivial)

theorem S2731PointScale_apply
    (point x : S2731Carrier (I := I) (V := V)) (v : V) :
    S2731PointScale (I := I) point x v = point v * x v := rfl

theorem S2731PointScaledRegion_eq
    (point : S2731Carrier (I := I) (V := V)) :
    S2731PointScaledRegion (I := I) point =
      S2731PointScale (I := I) point '' S2731UnitRegion (I := I) (V := V) := rfl

#check S2731Carrier
#check S2731UnitRegion
#check S2731PointScale
#check S2731PointScaledRegion
#check S2731Hull
#check S2731Image
#check S2731Image_subset_hull
#check S2731PointScale_apply
#check S2731PointScaledRegion_eq
#check S2731HullLogVolume
#print axioms S2731Image_subset_hull
#print axioms S2731PointScale_apply
#print axioms S2731PointScaledRegion_eq
#print axioms S2731HullLogVolume

end LeanFormal.IUT.XiFPaper.S2731PointScaledHullActual
end
