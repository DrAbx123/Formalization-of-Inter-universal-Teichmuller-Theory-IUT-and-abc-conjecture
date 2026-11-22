import tmp.sheaf.xif.paper.Mzk1P3AGREEFLTBridgeActual
import Mathlib.Tactic

/-! # CONDITIONAL: FLT global e*f = finrank wrapper -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3FLTMultiplicityActual

open IsDedekindDomain

/-- Wrapper around FLT BaseChange :751: global e*f equals the finrank of the
completion extension. -/
theorem FLT_ramificationIdx_mul_inertiaDeg_eq_finrank
    {A : Type*} (K : Type*) (L : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]
    {v : IsDedekindDomain.HeightOneSpectrum A}
    (w : IsDedekindDomain.HeightOneSpectrum.Extension B v)
    [FiniteDimensional K L] [Module.Finite A B] :
    (w.1.asIdeal).ramificationIdx A * (w.1.asIdeal).inertiaDeg A =
      Module.finrank (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w.1) :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank
    K L w

#check FLT_ramificationIdx_mul_inertiaDeg_eq_finrank
end LeanFormal.IUT.XiFPaper.Mzk1P3FLTMultiplicityActual
end
