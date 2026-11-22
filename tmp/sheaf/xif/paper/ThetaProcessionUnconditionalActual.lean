import tmp.sheaf.xif.paper.C3ActualThetaPacketWitnessConstruction
import tmp.sheaf.xif.paper.PaperSignedHullActual
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual
import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.xif.paper.SignedHnormalActual

/-!
# Unconditional theta packet/procession for the actual donor C3

Constructs, from the actual C3 built from source donors and the actual
theater theta packet:
* the actual theta packet;
* the actual unsigned procession;
* the actual signed procession;
* the actual signed PaperSignedHull, conditional only on its exact C6 Haar
  field hnormal.

The theta packet, unsigned procession, and signed procession are
unconditional actual objects. No inequality is asserted. The signed hull's
only missing field is SignedHnormal; no toy/axiom/sorry. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.ThetaProcessionUnconditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.C3ActualThetaPacketWitnessConstruction
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui uK uW

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

variable (D : SourcePilotRegionDonors (l := l) (V := V) I)

/-- The actual C3 object built from the source donors. -/
noncomputable abbrev actualDonorC3 :
    SourcePilotRegionData (l := l) (V := V) I :=
  actualC3OfDonors (I := I) D

/-- The actual theta packet of the donor C3 (the theater packet). -/
noncomputable def actualThetaPacket : FiniteThetaPacket l :=
  (actualDonorC3 (l := l) (V := V) (I := I) D).thetaPacket

/-- The actual theta-packet witness for the donor C3. -/
noncomputable def actualThetaPacketWitness :
    C3ActualThetaPacketWitness (I := I) :=
  actualC3ThetaPacketWitness (I := I) D

/-- The actual unsigned theta procession for the donor C3. -/
noncomputable def actualUnsignedProcession :
    WeightedValues (SignedLabel l.value) :=
  c3ThetaProcession (actualDonorC3 (l := l) (V := V) (I := I) D)

/-- The actual signed theta procession for the source-theater C3. -/
noncomputable def actualSignedProcession :
    WeightedValues (SignedLabel l.value) :=
  c3ThetaSignedProcession
    (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)

/-- The actual signed procession for the donor C3 itself. -/
noncomputable def actualDonorSignedProcession :
    WeightedValues (SignedLabel l.value) :=
  c3ThetaSignedProcession (actualDonorC3 (l := l) (V := V) (I := I) D)

/-- The exact missing C6 Haar field for the signed hull. -/
def MissingHnormal : Prop :=
  SignedHnormal (l := l) (V := V) (I := I) places tuple mu D

/-- The actual signed PaperSignedHull, conditional only on MissingHnormal. -/
noncomputable def actualSignedPaperHull
    (hnormal : MissingHnormal (l := l) (V := V) (I := I) places tuple mu D) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  actualSignedHull (l := l) (V := V) (I := I) places tuple mu D hnormal

/-- The conditional signed hull carries the actual signed procession. -/
theorem actualSignedPaperHull_procession_eq
    (hnormal : MissingHnormal (l := l) (V := V) (I := I) places tuple mu D) :
    (actualSignedPaperHull (l := l) (V := V) (I := I) places tuple mu D hnormal).procession =
      actualSignedProcession (l := l) (V := V) (I := I) D :=
  rfl

/- The only missing object for the signed PaperSignedHull is MissingHnormal;
/- the theta packet, unsigned procession, signed procession, and hull carrier
/- (given hnormal) are actual. No inequality is asserted. -/

#check actualThetaPacket
#check actualThetaPacketWitness
#check actualUnsignedProcession
#check actualSignedProcession
#check actualDonorSignedProcession
#check MissingHnormal
#check actualSignedPaperHull
#check actualSignedPaperHull_procession_eq

end LeanFormal.IUT.XiFPaper.ThetaProcessionUnconditionalActual

end
