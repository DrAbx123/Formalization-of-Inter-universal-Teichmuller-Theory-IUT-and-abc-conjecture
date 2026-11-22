import tmp.sheaf.n8.closure.SourceThetaToIQ
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2603C6RegionP4P5Actual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [MeasurableSpace (IQCarrier C3)]
variable [BorelSpace (IQCarrier C3)]
variable (mu : Measure (IQCarrier C3))
variable [Measure.IsAddHaarMeasure mu]
variable (n : ThetaPilotCarrier l)
variable (j : Nat -> Nat -> Nat -> SignedLabel l.value)

/-- The actual T11 theta image interface, built from C3's actual q-unit. -/
noncomputable def C6ThetaInterface :
    SourceThetaIQInterface (I := I) C3 :=
  thetaIQInterfaceOfQUnit (I := I) C3

/-- The actual C6 IQ data, from the actual finite-place Haar data. -/
noncomputable def C6Data : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu :=
  C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu

/-- The actual hull/region object: the theta-image singleton for an ABC triple. -/
noncomputable def C6ThetaRegion (a b c : Nat) : Set (IQCarrier C3) :=
  {((C6ThetaInterface I C3).thetaImage n (j a b c))}

/-- The actual full theta-image region at procession `n`. -/
noncomputable def C6ThetaImageSet : Set (IQCarrier C3) :=
  image (I := I) C3 (C6ThetaInterface I C3) n

/-- **P4 on the actual C6 hull/region object.**  Arithmetic weight is bounded
by the actual C6 normalized log-volume of the theta-image singleton region.
No raw `sourceThetaPilotPoint` log-degree is used. -/
def P4C6RegionWeightDictionary : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    arithmeticWeight (abcRationalPoint a c) <=
      (C6Data I C3 mu).normalizedLogVolume (C6ThetaRegion I C3 n j a b c)

/-- **P5 on the actual C6 hull/region object.**  The same C6 normalized
log-volume is compared with the canonical height. -/
def P5C6RegionHeightDictionary : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    (C6Data I C3 mu).normalizedLogVolume (C6ThetaRegion I C3 n j a b c) <=
      Height.logHeight₁ (abcRationalPoint a c)

/-- The C6 hull/region dictionary does not mention the raw theta-pilot
log-degree.  In particular the raw-point no-go hypothesis
`P4ThetaPilotWeightDictionary` is a different proposition; this definition is
anchored to `C6ActualIQData.normalizedLogVolume` and the T11 theta image. -/
theorem P4C6RegionWeightDictionary_eq_define :
    P4C6RegionWeightDictionary I C3 n j =
      (forall a b c : Nat, IsABCTriple a b c ->
        arithmeticWeight (abcRationalPoint a c) <=
          (C6Data I C3 mu).normalizedLogVolume
            {((C6ThetaInterface I C3).thetaImage n (j a b c))}) := rfl

#print axioms P4C6RegionWeightDictionary_eq_define

end LeanFormal.IUT.XiFPaper.S2603C6RegionP4P5Actual
end
