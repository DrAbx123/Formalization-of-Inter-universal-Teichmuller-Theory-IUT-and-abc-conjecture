import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option maxHeartbeats 4000000
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe15

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

#check @MorphismProperty.RespectsIso
#check @MorphismProperty.RespectsIso.cancel_left_isIso
#check @MorphismProperty.RespectsIso.cancel_right_isIso
#check @MorphismProperty.RespectsIso.of_isIso
#check @RingHom.finite_respectsIso
#check @RingHom.Etale.respectsIso
#check @Spec.map_inv
#check @Spec.map_iso
#check @Scheme.ΓSpecIso_inv_naturality
#check @Scheme.ΓSpecIso_hom_naturality
#check @RingHom.Finite
#check @RingHom.Finite.comp
#check @RingHom.Finite.stableUnderComposition
#check @Algebra.Etale
#check @Algebra.FormallyEtale
#check @Algebra.Etale.comp
#check @Algebra.Etale.of_equiv
#check @AlgEquiv.etale
#check @Algebra.Etale.iff_formallyEtale

end Probe15
