import tmp.sheaf.xif.paper.OModuleActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

/-! # CONDITIONAL STATUS (xi-f)

Conditional: actual unit line bundle/O-module/determinant are constructed, but the actual q-pilot ideal/line-bundle source identification is missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-! # Actual rank-one arithmetic line bundle / O-module / determinant layer

This file binds the actual rank-one fractional-ideal line bundle of
`OModuleActual.lean` and the actual determinant/log-volume data of
`DeterminantLogVolumeActual.lean` to the actual source arithmetic field of an
`InitialThetaArithmeticData`.

## Actual construction

* `SourceLineBundle A` is the actual fractional ideal `FractionalIdeal O_K A.K`.
* `unitLineBundle A = 1` is the actual unit fractional ideal (rank one,
  integral).
* `actualOModuleData` is `actualPaperLineBundleData` at that
  actual line bundle: actual `O_K`-module, finite-place localizations,
  determinant and p-adic local log-volume.
* `actualDeterminantData` is the actual fractional-ideal norm and global
  log-volume `Real.log (absNorm I)`.
* `PaperArithmeticLineBundleActual A` packages these with their exact
  definitional identifications.

## Exact missing source field

The paper q-pilot arithmetic line bundle is not produced by this unit ideal:
`InitialThetaArithmeticData` supplies the number field/curve, not the
q-pilot fractional ideal or its O-module class.  The exact missing datum is
the source q-pilot line-bundle identification
`PaperQPilotLineBundleSource.qPilot_lineBundle_identification`; no value is
chosen here.

No arbitrary real/carrier, `True`, `PUnit`, `sorry`, or axiom is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaperArithmeticLineBundle

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.PaperDeterminantLogVolume

variable {l : PrimeGeFive} (A : InitialThetaArithmeticData l)

/-- The actual number field K of the source arithmetic data. -/
abbrev SourceK : Type := A.K

/-- The actual integral ring O_K. -/
abbrev SourceOK : Type := NumberField.RingOfIntegers A.K

/-- Actual rank-one line bundles over the source arithmetic field: fractional
ideals of O_K in K. -/
abbrev SourceLineBundle : Type :=
  FractionalIdeal (nonZeroDivisors (SourceOK (A := A))) A.K

/-- The actual unit line bundle of the source arithmetic field. -/
def unitLineBundle : SourceLineBundle (A := A) :=
  (1 : FractionalIdeal (nonZeroDivisors (SourceOK (A := A))) A.K)

/-- The actual O-module data attached to the unit line bundle. -/
def actualOModuleData :
    PaperOModuleActual.PaperLineBundleData (k := A.K) :=
  actualPaperLineBundleData (k := A.K) (unitLineBundle (A := A))

/-- The actual determinant/log-volume data attached to the unit line bundle. -/
def actualDeterminantData :
    PaperDeterminantLogVolume.PaperDeterminantLogVolumeData (k := A.K) :=
  actualDeterminantLogVolumeData (k := A.K)
    (unitLineBundle (A := A))

@[simp] theorem actualOModuleData_lineBundle :
    (actualOModuleData (A := A)).lineBundle = unitLineBundle (A := A) := rfl

@[simp] theorem actualOModuleData_rank :
    (actualOModuleData (A := A)).rank = 1 := rfl

@[simp] theorem actualOModuleData_determinant :
    (actualOModuleData (A := A)).determinantLine = unitLineBundle (A := A) :=
  rfl

@[simp] theorem actualDeterminantData_lineBundle :
    (actualDeterminantData (A := A)).lineBundle = unitLineBundle (A := A) :=
  rfl

@[simp] theorem actualDeterminantData_determinantLine :
    (actualDeterminantData (A := A)).determinantLine = unitLineBundle (A := A) :=
  rfl

@[simp] theorem actualDeterminantData_globalLogVolume :
    (actualDeterminantData (A := A)).globalLogVolume =
      Real.log ((FractionalIdeal.absNorm (unitLineBundle (A := A)) : Rat) : Real) :=
  rfl

/-- The actual rank-one, O-module, localization, determinant and global
log-volume packet for a source arithmetic field. -/
structure PaperArithmeticLineBundleActual
    (A : InitialThetaArithmeticData l) where
  lineBundle : SourceLineBundle (A := A)
  rank : Nat
  rank_eq : rank = 1
  omData : PaperOModuleActual.PaperLineBundleData (k := A.K)
  detData : PaperDeterminantLogVolume.PaperDeterminantLogVolumeData (k := A.K)
  om_lineBundle_eq : omData.lineBundle = lineBundle
  det_lineBundle_eq : detData.lineBundle = lineBundle
  determinantLine_eq : detData.determinantLine = lineBundle
  globalLogVolume_eq : detData.globalLogVolume =
    Real.log ((FractionalIdeal.absNorm lineBundle : Rat) : Real)

namespace PaperArithmeticLineBundleActual

variable {A : InitialThetaArithmeticData l}

theorem rank_one (P : PaperArithmeticLineBundleActual A) : P.rank = 1 := P.rank_eq

theorem determinant_eq_line (P : PaperArithmeticLineBundleActual A) :
    P.detData.determinantLine = P.lineBundle := P.determinantLine_eq

theorem om_line_eq (P : PaperArithmeticLineBundleActual A) :
    P.omData.lineBundle = P.lineBundle := P.om_lineBundle_eq

theorem det_line_eq (P : PaperArithmeticLineBundleActual A) :
    P.detData.lineBundle = P.lineBundle := P.det_lineBundle_eq

theorem globalLogVolume_formula (P : PaperArithmeticLineBundleActual A) :
    P.detData.globalLogVolume =
      Real.log ((FractionalIdeal.absNorm P.lineBundle : Rat) : Real) :=
  P.globalLogVolume_eq

end PaperArithmeticLineBundleActual

/-- The actual unit-line-bundle packet for the source arithmetic field. -/
def actualUnitLineBundleData : PaperArithmeticLineBundleActual A where
  lineBundle := unitLineBundle (A := A)
  rank := 1
  rank_eq := rfl
  omData := actualOModuleData (A := A)
  detData := actualDeterminantData (A := A)
  om_lineBundle_eq := actualOModuleData_lineBundle (A := A)
  det_lineBundle_eq := actualDeterminantData_lineBundle (A := A)
  determinantLine_eq := actualDeterminantData_determinantLine (A := A)
  globalLogVolume_eq := actualDeterminantData_globalLogVolume (A := A)

@[simp] theorem actualUnitLineBundleData_lineBundle :
    (actualUnitLineBundleData (A := A)).lineBundle = unitLineBundle (A := A) :=
  rfl

@[simp] theorem actualUnitLineBundleData_rank :
    (actualUnitLineBundleData (A := A)).rank = 1 := rfl

@[simp] theorem actualUnitLineBundleData_globalLogVolume :
    (actualUnitLineBundleData (A := A)).detData.globalLogVolume =
      Real.log ((FractionalIdeal.absNorm (unitLineBundle (A := A)) : Rat) : Real) :=
  rfl

/-- The actual O_K-module instance on the source unit line bundle. -/
def unitLineBundleModule : Module (SourceOK (A := A)) (unitLineBundle (A := A)) :=
  PaperOModuleActual.lineBundleModule (k := A.K) (unitLineBundle (A := A))

/-- The actual localization map of the source unit line bundle at a finite
place. -/
def unitLocalizationMap (v : NumberField.FinitePlace A.K)
    (x : unitLineBundle (A := A)) :
    PaperOModuleActual.localizedLine (k := A.K) (unitLineBundle (A := A)) v :=
  PaperOModuleActual.localizationMap (k := A.K) (unitLineBundle (A := A)) v x

theorem unitLocalizationMap_mem (v : NumberField.FinitePlace A.K)
    (x : unitLineBundle (A := A)) :
    (algebraMap A.K (PaperOModuleActual.LocalField (k := A.K) v) (x : A.K)) ∈
      (PaperOModuleActual.localizedLine (k := A.K) (unitLineBundle (A := A)) v :
        Set (PaperOModuleActual.LocalField (k := A.K) v)) :=
  PaperOModuleActual.localizationMap_mem (k := A.K) (unitLineBundle (A := A)) v x

/-- The exact missing source identification: the paper q-pilot fractional
ideal/line bundle, its source ideal, and its O-module class.  This is a
structure field, not a proof. -/
structure PaperQPilotLineBundleSource (A : InitialThetaArithmeticData l) where
  qPilotLineBundle : SourceLineBundle (A := A)
  qPilotIdeal : Ideal (SourceOK (A := A))
  qPilot_lineBundle_eq : qPilotLineBundle =
    (qPilotIdeal : FractionalIdeal (nonZeroDivisors (SourceOK (A := A))) A.K)
  qPilot_source_identification : Prop

end XiFPaperArithmeticLineBundle
end LeanFormal.IUT

end
