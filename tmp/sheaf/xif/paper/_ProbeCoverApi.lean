import tmp.sheaf.xif.paper.Mzk1G1FermatTwoChartGluingActual
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open AlgebraicGeometry CategoryTheory

namespace ProbeCover

variable (n : Nat)

#check @IsZariskiLocalAtSource.iff_of_openCover
#check @IsZariskiLocalAtSource.iff_of_iSup_eq_top
#check (LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual.fermatIdx1 n : (LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual.fermatTwoChartGlueData n).openCover.I₀)
#check (LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual.fermatTwoChartGlueData n).openCover.f (LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual.fermatIdx1 n)

end ProbeCover
