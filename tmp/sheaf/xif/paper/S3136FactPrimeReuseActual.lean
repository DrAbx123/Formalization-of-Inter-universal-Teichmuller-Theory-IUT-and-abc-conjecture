import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

/-! # Stage-4 host: reuse of the prior-art Fact-prime instance

PRIOR ART (§7.9): LeanFormal/IUT/ABCBridge/Geometry/FinitePlacePadicScalarStructure.lean:28-29
provides instance completionRationalPrime_fact :
Fact (completionRationalPrime place).val.Prime for every finite place.

CONSUMER: any stage-4 fact needing the rational prime's primality. Our
qVFamTensorCoefficientActual defines qVFamTensorP := (completionRationalPrime
(qVFamTensorPlace T b)).val with instance qVFamTensorPFact proved via .property;
the prior-art instance is the same data, so consumers should use the shared
instance rather than re-derive primality.

LABEL: reuse adapter (no new proof). Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136FactPrimeReuseActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The shared prior-art Fact instance gives the qVFam tensor prime's primality. -/
theorem lgpQVFamTensorP_prime_via_priorArt :
    (qVFamTensorP T b).Prime :=
  (completionRationalPrime_fact (qVFamTensorPlace T b)).out

/-- The existing qVFam tensor Fact instance is the same statement. -/
theorem lgpQVFamTensorP_prime_via_local :
    (qVFamTensorP T b).Prime :=
  (qVFamTensorPFact T b).out

#check lgpQVFamTensorP_prime_via_priorArt
#check lgpQVFamTensorP_prime_via_local
#check completionRationalPrime_fact

end LeanFormal.IUT.XiFPaper.S3136FactPrimeReuseActual
end