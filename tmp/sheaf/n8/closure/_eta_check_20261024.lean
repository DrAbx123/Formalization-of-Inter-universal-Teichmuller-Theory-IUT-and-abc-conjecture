import tmp.sheaf.n8.closure.EtaRegionAdmCorrect
import tmp.sheaf.n8.closure.P6AdmRedesign
import tmp.sheaf.n8.closure.P6NonarchAdmActual

noncomputable section
namespace Check
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6AdmRedesign
open LeanFormal.IUT.N8Closure.EtaRegionAdmCorrect
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)]
variable (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v → IsUltrametricDist (localFieldAt X v))
variable (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v → ProperSpace (localFieldAt X v))

include mu hultra hproperFinite

#check @integralReference_measurable
#check @integralReference_pos
#check @integralReference_finite
#check @correctedRegion_measurable
#check @etaRegionAdmCorrect

end Check
