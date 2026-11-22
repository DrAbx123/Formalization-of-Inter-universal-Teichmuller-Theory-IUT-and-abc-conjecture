import tmp.sheaf.xif.paper.S2613DetCyclotomicInterfaceActual
import tmp.sheaf.xif.paper.S2617SignDetActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

namespace LeanFormal.IUT.XiFPaper.S2618RangeDetActual

open LeanFormal.IUT.XiFPaper.S2613DetCyclotomicInterfaceActual
open LeanFormal.IUT.XiFPaper.S2617SignDetActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual

/-- A 12-cycle in the actual range gives determinant surjectivity on that range. -/
theorem S2618DetSurjective_of_range_cycle12
    (h : GL2)
    (hh : h ∈ (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range)
    (hc : (pairPermHom h).cycleType = ({12} : Multiset ℕ)) :
    S2613DetSurjectiveRemaining :=
  S2617DetSurjective_of_twelveCycle _ h hh hc

end LeanFormal.IUT.XiFPaper.S2618RangeDetActual
end