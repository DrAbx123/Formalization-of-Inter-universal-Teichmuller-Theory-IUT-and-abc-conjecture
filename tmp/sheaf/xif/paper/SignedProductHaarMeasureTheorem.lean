import tmp.sheaf.xif.paper.SignedProductHaarUnconditional
import tmp.sheaf.xif.paper.SignedHnormalActual

/-!
# Signed product-Haar measure theorem: exact status

The signed product-Haar theorem is exactly

  arithmeticTupleHullUnitLogVolume places tuple
    = (c3ThetaSignedProcession actualSignedC3).average
      - log(mu canonicalUnitReference).toReal.

The actual product/Fubini specification of `arithmeticTupleHullUnitLogVolume`
is available unconditionally (with existence and uniqueness). What is missing
is the identification of its fundamental-domain normalized volume with the
signed theta average minus the unit-reference log. No theorem in the current
source identifies these two quantities; Fubini/product decomposition only
identifies different field-product realizations of the same unit log-volume.

This file records the exact missing measure theorem and proves its
equivalence with the product/Fubini specification using the actual
existence/uniqueness theorem. No fake proof, inequality, or axiom. WRITE-ONLY:
no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.SignedProductHaarMeasureTheorem

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.SignedHnormalObjectActual
open LeanFormal.IUT.XiFPaper.SignedProductHaarThetaActual
open LeanFormal.IUT.XiFPaper.SignedProductHaarUnconditional
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

/-- Exact missing theorem, in product/Fubini form: the actual fundamental-
/-- domain volume has value signedAverage - log unitReference. -/
def MissingFundamentalDomainVolumeIdentity : Prop :=
  ActualProductHaarSpec (l := l) (V := V) (I := I) places tuple mu D

/-- The same theorem in scalar form. -/
def MissingScalarProductHaarIdentity : Prop :=
  MissingActualProductHaarMeasureIdentity (l := l) (V := V) (I := I)
    places tuple mu D

/-- The product/Fubini form and the scalar form are equivalent, by the actual
/-- existence and uniqueness of the unit log-volume specification. -/
theorem missingFundamentalDomainVolumeIdentity_iff_scalar :
    MissingFundamentalDomainVolumeIdentity (l := l) (V := V) (I := I)
      places tuple mu D ↔
      MissingScalarProductHaarIdentity (l := l) (V := V) (I := I)
        places tuple mu D := by
  exact missingActualProductHaarMeasureIdentity_iff_spec
    (l := l) (V := V) (I := I) places tuple mu D

/-- The unconditional product-Haar data object from task-637. -/
abbrev actualProductHaarDataObject :
    ActualProductHaarData (l := l) places tuple mu :=
  actualProductHaarData (l := l) (V := V) (I := I) places tuple mu (D := D)

/-- The exact missing theorem is not a consequence of the unconditional
/-- product-Haar data alone: the data provides the spec at the chosen unit
/-- log-volume, while the missing identity is the signed-average evaluation.
The equivalence above is the complete reduction. -/

#check MissingFundamentalDomainVolumeIdentity
#check MissingScalarProductHaarIdentity
#check missingFundamentalDomainVolumeIdentity_iff_scalar
#check actualProductHaarDataObject
#check ActualProductHaarData
#check actualSignedProductHaarObject

end LeanFormal.IUT.XiFPaper.SignedProductHaarMeasureTheorem

end
