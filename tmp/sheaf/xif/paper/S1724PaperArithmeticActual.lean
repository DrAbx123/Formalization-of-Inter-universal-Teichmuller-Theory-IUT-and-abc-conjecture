import tmp.sheaf.xif.paper.S1721TorsionBaseChangeActual
import tmp.sheaf.xif.paper.S1722DegreePrimeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1721TorsionBaseChangeActual
open LeanFormal.IUT.XiFPaper.S1722DegreePrimeActual

namespace LeanFormal.IUT.XiFPaper.S1724PaperArithmeticActual

/-- The actual source arithmetic's torsion condition, from S1721. -/
theorem S1724Torsion23 : S1720Torsion23Missing :=
  S1721S1720Torsion23Missing

/-- The complete paper arithmetic data, unconditional. -/
noncomputable def S1724PaperArithmeticData (l : PrimeGeFive) :
    S1720PaperArithmeticData l :=
  S1722PaperArithmeticData_of_torsion l S1724Torsion23

/-- The initial Theta arithmetic data, unconditional. -/
noncomputable def S1724InitialThetaArithmeticData (l : PrimeGeFive) :
    InitialThetaArithmeticData l :=
  S1722InitialThetaArithmeticData l

#print axioms S1724Torsion23
#print axioms S1724PaperArithmeticData
#print axioms S1724InitialThetaArithmeticData

end LeanFormal.IUT.XiFPaper.S1724PaperArithmeticActual
