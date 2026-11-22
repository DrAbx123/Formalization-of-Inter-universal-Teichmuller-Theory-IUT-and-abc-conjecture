import Mathlib
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory

noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace Probe

universe u

#check @CategoryTheory.Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback
#check @CategoryTheory.Limits.Types.isPullback_iff
#check @CategoryTheory.Limits.Types.isPushout_iff
#check @CategoryTheory.Limits.coyonedaPreservesLimitsOfShape
#check @CategoryTheory.Limits.preservesLimitsOfShape_of_natIso
#check @CategoryTheory.Over.Hom
#check @CategoryTheory.Over.mk
#check @CategoryTheory.Over.homMk
#check @CategoryTheory.Limits.Types.binaryCofanIsColimit
#check @CategoryTheory.Limits.Types.binaryCofan_isColimit_iff
#check @CategoryTheory.Limits.BinaryCofan.IsColimit.mk
#check @CategoryTheory.Limits.IsColimit.ofIsoColimit
#check @CategoryTheory.Limits.BinaryCofan.ext
#check @Scheme.coprodMk
#check @Scheme.isCompl_range_inl_inr
#check @AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift
#check @AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac
#check @AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq
#check @AlgebraicGeometry.Scheme.Opens.toScheme
#check @AlgebraicGeometry.Scheme.Opens.ι
#check @PrimeSpectrum.instUnique
#check @PrimeSpectrum.unique
#check @AlgebraicGeometry.Spec
#check @CategoryTheory.Limits.HasColimit
#check @CategoryTheory.Limits.PreservesFiniteCoproducts
#check @CategoryTheory.Limits.PreservesFiniteCoproducts.of_preserves_binary_and_initial
#check @CategoryTheory.Limits.preservesColimitsOfShape_pempty_of_preservesInitial

end Probe
