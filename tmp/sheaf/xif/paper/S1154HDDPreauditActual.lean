import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRealization
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import tmp.sheaf.xif.paper.GlobalKummerIndActionsActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1154HDDPreauditActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual

-- Capsule/procession donors.
#check H2FProcession.canonical
#check H2FProcession.canonical_stage_strip
#check H2FProcession.canonical_stage_link
#check H2FProcession.spokeTransport

-- Local-field / arithmetic holomorphic donors.
#check SourceOneColumnArithmeticHolomorphicStructure
#check SourceArithmeticVectorBundle
#check SourceLocalizationExpressible
#check actualOneColumnFinitePrimePlace

-- Finite tensor/hull actual realization.
#check exists_realized_tensorLogShell_hull

-- Kummer/Ind actual action donors.
#check globalKummerIndActionsData

end LeanFormal.IUT.XiFPaper.S1154HDDPreauditActual

end
