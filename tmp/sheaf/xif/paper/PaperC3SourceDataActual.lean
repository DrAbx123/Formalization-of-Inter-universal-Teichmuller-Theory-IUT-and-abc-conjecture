import tmp.sheaf.xif.paper.PaperC3TensorGeometryActual
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier

-- Actual SourcePilotRegionData / PaperC3Data on the nondegenerate tensor geometry
--
-- q: actual FinitePlaceQCandidate at G.place v (Classical.choice of the proved
--    existence theorem), not a Real/toy scalar.
-- thetaPacket: actual source-theater FiniteThetaPacket.
-- tensor index/places: nondegenerate PaperC3TensorGeometryActual (V, G.place).
-- roots/root systems/Kummer towers/tensorUnit/tensorLanding: exact actual inputs
--    of the corresponding source data; no fake inhabitants are supplied.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperC3SourceDataActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open LeanFormal.IUT.IUTII.Frobenioid
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier

universe ua upi umon ui u

variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable {p : Nat} [Fact p.Prime]
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := I.initial.arithmetic.Fmod) (p := p) V)
variable (v : V)

-- Actual q candidate at the selected geometry place.
noncomputable def paperC3Q :
    FinitePlaceQCandidate (G.place v).val :=
  Classical.choice (finitePlaceQCandidate_nonempty (G.place v).val)

-- Actual q unit.
noncomputable def paperC3QUnit :
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) (G.place v))ˣ :=
  candidateUnits (K := I.initial.arithmetic.Fmod) (G.place v) (paperC3Q G v)

-- Conditional actual C3 data: q/theta/tensor geometry are actual; roots, Kummer
-- towers, tensor unit and tensor landing are exact source inputs.
noncomputable def paperC3SourceData
    (roots roots' : NatRootSystem (paperC3QUnit (I := I) G v))
    (kummerClass rootChange :
      CyclotomicTower (CommonPrimeCompletion
        (K := I.initial.arithmetic.Fmod) (G.place v)))
    (rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots')
    (tensorUnit : (ArithmeticTensorTupleBlock (fun i (_ : Unit) => G.place i) (fun _ => ()))ˣ)
    (tensorLanding :
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) (G.place v) →
        ArithmeticTensorTupleBlock (fun i (_ : Unit) => G.place i) (fun _ => ()))
    (tensorLanding_q :
      tensorLanding ((paperC3Q (I := I) G v).q :
        CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) (G.place v)) =
        (tensorUnit : ArithmeticTensorTupleBlock (fun i (_ : Unit) => G.place i) (fun _ => ()))) :
    SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I where
  p := p
  place := G.place v
  q := paperC3Q (I := I) G v
  thetaPacket := (sourceTheater l).thetaPacket
  qUnit := paperC3QUnit (I := I) G v
  qUnit_eq := rfl
  roots := roots
  roots' := roots'
  kummerClass := kummerClass
  rootChange := rootChange
  rootChange_eq := rootChange_eq
  tensorIndex := PaperTensorIndex (V := V)
  tensorFintype := inferInstance
  tensorPlaceIndex := PaperTensorPlaceIndex (V := V)
  tensorPlaces := paperTensorPlaces (G := G)
  tensorTuple := paperTensorTuple
  tensorUnit := tensorUnit
  tensorLanding := tensorLanding
  tensorLanding_q := tensorLanding_q

-- q/theta are actual; only roots/Kummer/tensor unit/landing are exact inputs.
theorem paperC3SourceData_q :
    (paperC3SourceData (I := I) G v roots roots' kummerClass rootChange
      rootChange_eq tensorUnit tensorLanding tensorLanding_q).q =
      paperC3Q (I := I) G v := rfl

theorem paperC3SourceData_thetaPacket :
    (paperC3SourceData (I := I) G v roots roots' kummerClass rootChange
      rootChange_eq tensorUnit tensorLanding tensorLanding_q).thetaPacket =
      (sourceTheater l).thetaPacket := rfl

#check paperC3Q
#check paperC3QUnit
#check paperC3SourceData
#check paperC3SourceData_q
#check paperC3SourceData_thetaPacket

end LeanFormal.IUT.XiFPaper.PaperC3SourceDataActual

end