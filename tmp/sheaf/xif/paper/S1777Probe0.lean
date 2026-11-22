import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe

#check @CommAlgCat.FiniteEtale
#check @CommAlgCat.FiniteEtale.of
#check @CommAlgCat.FiniteEtale.ofHom
#check @CommAlgCat.FiniteEtale.isoMk
#check @S1733Slice
#check @S1733FiniteEtale
#check @MorphismProperty.CostructuredArrow
#check @MorphismProperty.CostructuredArrow.mk
#check @MorphismProperty.CostructuredArrow.homMk
#check @MorphismProperty.CostructuredArrow.toOver
#check @Scheme.ΓSpecIso
#check @Scheme.Spec
#check @AlgebraicGeometry.Scheme.Spec
#check @AlgebraicGeometry.Spec.map
#check @AlgebraicGeometry.Spec.map_injective
#check @AlgebraicGeometry.Spec.map_comp
#check @HasAffineProperty.iff_of_isAffine
#check @AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine
#check @AlgebraicGeometry.IsFinite.iff_of_isAffine
#check @RingHom.Finite
#check @RingHom.finite_algebraMap
#check @AlgebraicGeometry.IsFinite.SpecMap_iff
#check @AlgebraicGeometry.Etale
#check @AlgebraicGeometry.HasRingHomProperty.Spec_iff
#check @AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine
#check @RingHom.etale_algebraMap
#check @AlgebraicGeometry.Scheme.isoSpec
#check @AlgebraicGeometry.Scheme.isoSpec_hom_naturality
#check @AlgebraicGeometry.arrowIsoΓSpecOfIsAffine
#check @AlgebraicGeometry.arrowIsoSpecΓOfIsAffine
#check @AlgebraicGeometry.AffineScheme.Spec
#check @AlgebraicGeometry.AffineScheme.Γ
#check @AlgebraicGeometry.AffineScheme.equivCommRingCat

end Probe
