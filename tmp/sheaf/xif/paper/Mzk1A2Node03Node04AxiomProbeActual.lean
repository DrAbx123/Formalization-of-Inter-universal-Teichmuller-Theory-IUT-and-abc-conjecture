/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03IntegrationConsumerActual
import tmp.sheaf.xif.paper.Mzk1A2Node03CompletionConsumerActual
import tmp.sheaf.xif.paper.Mzk1A2Node04HandoffConsumerActual
import tmp.sheaf.xif.paper.Mzk1A2Node04LocalTransportConsumerActual

/-! # A2 node03/04 axiom probe -/
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03QuotientStackProducerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03QuotientStackConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceWitnessConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03IntegrationConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03CompletionConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node04HandoffConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node04LocalTransportConsumerActual

#print axioms A2QuotientStackProducerData.toWitness
#print axioms A2Node03QuotientStackConsumerData.nonempty_witness
#print axioms sourceSignQuotientDataWithProducerWitness
#print axioms LeanFormal.IUT.XiFPaper.Mzk1A2Node03IntegrationActual.A2Node03Interface.toWitness
#print axioms A2Node04HandoffData.toSourceSignQuotientData
#print axioms A2Node04LocalTransportInterface.toSourceCompletionSignQuotient

end
