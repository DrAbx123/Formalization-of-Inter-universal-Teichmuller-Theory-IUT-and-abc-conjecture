import tmp.sheaf.xif.paper.QPilotGlobalLineBundleActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.xif.paper.OModuleActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual

/-!
# Actual q-pilot rank-one arithmetic line bundle target

IUT III, Definition 3.8, (i), pp. 112-113 and IUT III, p. 17: the q-pilot is
the arithmetic divisor determined by the zero locus of the q_v, and its
arithmetic line bundle has log-volume -|log q|.  IUT III, pp. 131-135 explains
the determinant/line-bundle normalization.

This file constructs the actual paper-level q-pilot rank-one line-bundle
packet over the base Fmod field from the actual zero-locus construction:

* qPilotZeroLocusIdeal: product of the actual bad base prime ideals;
* qPilotLineBundle: the actual fractional ideal O(-D), inverse of the
  zero-locus ideal;
* qPilotOModuleData: the actual PaperLineBundleData with rank 1, actual local
  rings/lines, determinant and localization;
* qPilotDeterminantData: the actual PaperDeterminantLogVolumeData;
* PaperQPilotLineBundleActual: the packed actual target with actual
  rank/rank_eq, O-module data, determinant data and global log-volume formula;
* qPilotPaperLineBundleActual: the actual inhabitant.

No inequality, no empty type, no arbitrary rank data: the rank field is the
standard actual packet rank 1, matching OModuleActual.  No toy/True/PUnit/
axiom/sorry.  WRITE-ONLY; no local compile; queued.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QPilotPaperLineBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QPilotGlobalLineBundleActual
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.PaperDeterminantLogVolume

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- The actual base field Fmod of the q-pilot line bundle. -/
abbrev QPilotBaseField : Type := X.S.arithmetic.Fmod

/-- The actual zero-locus q-pilot ideal in O_Fmod. -/
noncomputable def qPilotZeroLocusIdeal :
    Ideal (NumberField.RingOfIntegers (QPilotBaseField X)) :=
  qPilotGlobalIdeal X

/-- The actual q-pilot line bundle O(-D), inverse of the zero-locus ideal. -/
noncomputable def qPilotLineBundle :
    PaperOModuleActual.LineBundle (k := QPilotBaseField X) :=
  qPilotGlobalLineBundle X

/-- The line bundle is exactly the inverse of the zero-locus fractional ideal. -/
theorem qPilotLineBundle_eq_inv_zeroLocus :
    qPilotLineBundle X =
      (qPilotZeroLocusIdeal X : FractionalIdeal
        (nonZeroDivisors (NumberField.RingOfIntegers (QPilotBaseField X)))
        (QPilotBaseField X))⁻¹ := rfl

/-- The actual rank-one O-module/localization data of the q-pilot line bundle. -/
noncomputable def qPilotOModuleData :
    PaperLineBundleData (k := QPilotBaseField X) :=
  actualPaperLineBundleData (k := QPilotBaseField X) (qPilotLineBundle X)

/-- The actual determinant/log-volume data of the q-pilot line bundle. -/
noncomputable def qPilotDeterminantData :
    PaperDeterminantLogVolumeData (k := QPilotBaseField X) :=
  actualDeterminantLogVolumeData (k := QPilotBaseField X) (qPilotLineBundle X)

/-- Actual O_Fmod-module structure on the q-pilot line bundle. -/
noncomputable def qPilotLineBundleModule :
    Module (NumberField.RingOfIntegers (QPilotBaseField X)) (qPilotLineBundle X) :=
  lineBundleModule (k := QPilotBaseField X) (qPilotLineBundle X)

/-- The packed actual q-pilot rank-one arithmetic line-bundle target. -/
structure PaperQPilotLineBundleActual where
  zeroLocusIdeal : Ideal (NumberField.RingOfIntegers (QPilotBaseField X))
  lineBundle : PaperOModuleActual.LineBundle (k := QPilotBaseField X)
  lineBundle_eq_inv_zeroLocus : lineBundle =
    (zeroLocusIdeal : FractionalIdeal
      (nonZeroDivisors (NumberField.RingOfIntegers (QPilotBaseField X)))
      (QPilotBaseField X))⁻¹
  rank : Nat
  rank_eq : rank = 1
  omData : PaperLineBundleData (k := QPilotBaseField X)
  detData : PaperDeterminantLogVolumeData (k := QPilotBaseField X)
  om_lineBundle_eq : omData.lineBundle = lineBundle
  det_lineBundle_eq : detData.lineBundle = lineBundle
  determinantLine_eq : detData.determinantLine = lineBundle
  globalLogVolume_eq : detData.globalLogVolume =
    Real.log ((FractionalIdeal.absNorm lineBundle : Rat) : Real)

/-- The actual q-pilot rank-one arithmetic line-bundle target. -/
noncomputable def qPilotPaperLineBundleActual :
    PaperQPilotLineBundleActual X where
  zeroLocusIdeal := qPilotZeroLocusIdeal X
  lineBundle := qPilotLineBundle X
  lineBundle_eq_inv_zeroLocus := rfl
  rank := 1
  rank_eq := rfl
  omData := qPilotOModuleData X
  detData := qPilotDeterminantData X
  om_lineBundle_eq := rfl
  det_lineBundle_eq := rfl
  determinantLine_eq := rfl
  globalLogVolume_eq := rfl

/-- The actual target's rank is one. -/
theorem qPilotPaperLineBundleActual_rank :
    (qPilotPaperLineBundleActual X).rank = 1 := rfl

/-- The actual target's line bundle is O(-D). -/
theorem qPilotPaperLineBundleActual_lineBundle :
    (qPilotPaperLineBundleActual X).lineBundle = qPilotLineBundle X := rfl

/-- The actual target's global log-volume is the actual line-bundle log-volume. -/
theorem qPilotPaperLineBundleActual_globalLogVolume :
    (qPilotPaperLineBundleActual X).detData.globalLogVolume =
      Real.log ((FractionalIdeal.absNorm (qPilotLineBundle X) : Rat) : Real) :=
  rfl

end LeanFormal.IUT.XiFPaper.QPilotPaperLineBundleActual
