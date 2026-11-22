import tmp.sheaf.xif.paper.S2826Torsion23Fresh
import tmp.sheaf.xif.paper.S2810F6GaloisTorsionActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2790F6Actual

-- exact-target checks (definitional unfolding of the three target spellings)
example : LeanFormal.IUT.XiFPaper.S2810F6GaloisTorsionActual.S2810Torsion23Target :=
  S2826_torsion23
example : S2812Torsion23Target := S2826_torsion23
example : S2790Torsion23Target := S2826_torsion23
#check (S2826_torsion23 : LeanFormal.IUT.XiFPaper.S2810F6GaloisTorsionActual.S2810Torsion23Target)
#print axioms S2826_torsion23
