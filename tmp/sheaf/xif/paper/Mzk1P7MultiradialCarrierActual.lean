import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteMultiradial
import LeanFormal.IUT.IUTIII.Theorem311.Output.MultiradialAlgorithmReduction

/-!
# GAP-P7-MULTIRADIAL: reused finite multiradial carrier (model only)

Port source:
* LeanFormal/IUT/IUTIII/Theorem311/MultiradialOutputKernel.lean
  (MultiradialKernel.Core/Profile, Ind1/2/3 kernel laws);
* LeanFormal/IUT/IUTIII/Theorem311/SourceFiniteMultiradial.lean
  (finite Q(i)-at-5 concrete carrier: core l / profile l);
* LeanFormal/IUT/IUTIII/Theorem311/Output/MultiradialAlgorithmReduction.lean
  (kernel-level algorithm contract; conditional on the source package).

Semantics warning: this is the finite/kernel model only.  It is NOT the
paper's xi-e/xi-f multiradial production on actual Hodge theaters/F-prime-
strips.  The finite model header itself records this boundary.  No actual
production object or output type is constructed here.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceFiniteMultiradial
open LeanFormal.IUT.ConcreteFiniteTheorem311

/-- Reused finite multiradial core carrier (model only). -/
noncomputable abbrev finiteCore (l : PrimeGeFive) :=
  SourceFiniteMultiradial.core l

/-- Reused finite multiradial profile carrier (model only). -/
noncomputable abbrev finiteProfile (l : PrimeGeFive) :=
  SourceFiniteMultiradial.profile l

/-- The finite profile's log-volume formula, re-exported from the model. -/
theorem finiteProfile_logVolume_formula (l : PrimeGeFive)
    (c : ConcreteFiniteTheorem311.ProcessionChoice l) :
    (finiteProfile l).logVolume c =
      ConcreteFiniteTheorem311.thetaLogVolume l + (c.upperSemiLevel : Real) :=
  SourceFiniteMultiradial.profile_logVolume_formula l c


/-- Finite Q(i)-at-5 production bundle (model only): algorithm contract +
route normal form + Ind1/2/3 quotient laws, extracted from
MultiradialAlgorithmReduction.finiteMultiradialAlgorithmDischarge. -/
def finiteMultiradialAlgorithmDischarge_model (l : PrimeGeFive) :=
  LeanFormal.IUT.MultiradialAlgorithmReduction.finiteMultiradialAlgorithmDischarge l

/-- Finite Ind1/Ind2/Ind3 quotient laws (model only), extracted from
MultiradialAlgorithmReduction.finiteIndeterminacyDischarge. -/
def finiteIndeterminacyDischarge_model (l : PrimeGeFive) :=
  LeanFormal.IUT.MultiradialAlgorithmReduction.finiteIndeterminacyDischarge l

#print axioms finiteMultiradialAlgorithmDischarge_model
#print axioms finiteIndeterminacyDischarge_model

#print axioms finiteProfile_logVolume_formula

end LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialCarrierActual
