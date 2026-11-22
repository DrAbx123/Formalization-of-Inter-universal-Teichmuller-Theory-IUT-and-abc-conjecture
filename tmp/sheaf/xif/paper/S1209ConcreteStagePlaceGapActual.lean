import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1209ConcreteStagePlaceGapActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceProcessionBoundary
open LeanFormal.IUT.SourceProcessionBoundary.Input
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

-- Concrete boundary input and its type shape.
#check concreteInput
#check SourceProcessionBoundary.Input
#check SourceFiniteParameterized.Choice
#check ConcreteFiniteTheorem311.ProcessionChoice

-- Concrete finite-prime-place instance.
#check actualOneColumnFinitePrimePlace
#check finitePrimePlaceToQ

-- Stage capsule fields available only on an OriginalInput.
#check FStageCapsule.source
#check FStageCapsule.strip
#check H2FProcession.canonical

end LeanFormal.IUT.XiFPaper.S1209ConcreteStagePlaceGapActual

end
