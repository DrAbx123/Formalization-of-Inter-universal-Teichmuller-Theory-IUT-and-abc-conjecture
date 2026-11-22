import tmp.sheaf.xif.paper.S2563DiscrMatrixActual

noncomputable section

set_option maxHeartbeats 16000000

open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2563Consumer

open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual

/-- The locked target, restated from the compiled module. -/
theorem target :
    LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Dval =
      Polynomial.discr LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ :=
  LeanFormal.IUT.XiFPaper.S2563DiscrMatrixActual.Dval_eq_discr

/-- The same statement in the reverse orientation. -/
theorem target' :
    Polynomial.discr LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ =
      LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Dval :=
  LeanFormal.IUT.XiFPaper.S2563DiscrMatrixActual.discr_eq

#print axioms target
#print axioms target'

end LeanFormal.IUT.XiFPaper.S2563Consumer

end
