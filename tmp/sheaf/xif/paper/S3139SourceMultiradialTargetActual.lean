import tmp.sheaf.xif.paper.S3139SourceMultiradialQuotientActual
import tmp.sheaf.xif.paper.S3139SourceMultiradialConsumerActual

/-!
# S3139: multiradial-representation target (umbrella module)

The actual partial multiradial representation of IUT III, Theorem 3.11(i) is
split by topic into two modules (each under 200 lines):

* `S3139SourceMultiradialQuotientActual`: the generated (Ind1)+(Ind2)
  quotient carrier of the actual source core, with the descended
  log-volume/possible-image/level readouts and the (Ind1)/(Ind2)/(Ind3) laws;
* `S3139SourceMultiradialConsumerActual`: the named
  `SourceMultiradialTargetInput` record for the lattice/mainline consumers,
  the etale-like radial target of the actual 0-column etHT, and the named
  `SourceQThetaComparisonInput` whose conclusion is the Corollary 3.12
  ordered q/Theta comparison.

Source: Formalization of IUT (2026-04) §4 :505-524, :536-546, :602-621.
The first-triangle mutation BPS -> quotient target remains the exact Missing
object recorded in `S3139StageOneSeamsActual.SourceMultiradialMutationDemand`.
-/

open LeanFormal.IUT

#check LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual.SourceMultiradialCarrier
#check LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual.sourceMultiradialMap_ind1
#check LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual.sourceMultiradialPossibleImage_ind3_upper
#check LeanFormal.IUT.XiFPaper.S3139SourceMultiradialConsumerActual.SourceMultiradialTargetInput
#check LeanFormal.IUT.XiFPaper.S3139SourceMultiradialConsumerActual.sourceMultiradialTargetInput
#check LeanFormal.IUT.XiFPaper.S3139SourceMultiradialConsumerActual.SourceQThetaComparisonInput.conclusion
