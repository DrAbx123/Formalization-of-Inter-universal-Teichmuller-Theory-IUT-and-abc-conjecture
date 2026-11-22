import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
set_option maxHeartbeats 4000000
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe16

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

#check @RingHom.RespectsIso
#check @RingHom.RespectsIso.toIso
#check @RingHom.RespectsIso.iff_of_ringEquiv
#check @RingHom.RespectsIso.iso
#check @RingHom.Finite.of_bijective
#check @RingHom.Etale.of_bijective
#check @RingHom.Etale.stableUnderComposition
#check @RingHom.Finite.stableUnderComposition
#check @RingHom.Finite.of_isIso
#check @RingHom.Etale.of_isIso
#check @RingHom.Etale.comp
#check @RingHom.Etale.finite
#check @Algebra.Etale.of_bijective
#check @RingHom.Etale.of_comp
#check @RingHom.Finite.of_comp

end Probe16
