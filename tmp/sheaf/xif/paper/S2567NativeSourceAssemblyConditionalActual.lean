import tmp.sheaf.n8.closure.NativeSourceAssembly
import tmp.sheaf.n8.closure.NativeBadFintypeClosed

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual
open LeanFormal.IUT.InitialThetaSource.NativeSourceTorsion
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.N8Closure.C1Actual

namespace LeanFormal.IUT.XiFPaper.S2567NativeSourceAssemblyConditionalActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Conditional NativeSourceAssembly: every remaining field is an explicit exact source input. -/
noncomputable def S2567NativeSourceAssembly
    (badFinite : NativeBadSetFinite X.S)
    (split : NativeSplitMultiplicativeAtLift X.S)
    (torsionGaps : NativeSourceTorsionGaps (D := X.S.clauseC))
    (exactSequence : LeanFormal.IUT.Theorem311Source.SourceExactSequenceClause)
    (curve puncturedCurve cover structureGroup : Type)
    [Group structureGroup]
    (curveToPunctured : puncturedCurve → curve)
    (coverToPunctured : cover → puncturedCurve)
    (cover_surjective : Function.Surjective coverToPunctured)
    (cuspCount : Nat) (cuspCount_pos : 0 < cuspCount)
    (d7 : NativeD7Intake (SourceCompletion.ofSourceNative X.S))
    (cuspHyp : NativeCuspClauseHypotheses)
    (redCompat : Prop) (redCompat_proved : redCompat)
    (torCompat : Prop) (torCompat_proved : torCompat)
    (orbCompat : Prop) (orbCompat_proved : orbCompat)
    (secCompat : Prop) (secCompat_proved : secCompat)
    (cusCompat : Prop) (cusCompat_proved : cusCompat) :
    NativeSourceAssembly X.S where
  badFinite := badFinite
  split := split
  torsionGaps := torsionGaps
  exactSequence := exactSequence
  curve := curve
  puncturedCurve := puncturedCurve
  cover := cover
  structureGroup := structureGroup
  structureGroupLaw := inferInstance
  curveToPunctured := curveToPunctured
  coverToPunctured := coverToPunctured
  cover_surjective := cover_surjective
  cuspCount := cuspCount
  cuspCount_pos := cuspCount_pos
  d7 := d7
  cuspHyp := cuspHyp
  redCompat := redCompat
  redCompat_proved := redCompat_proved
  torCompat := torCompat
  torCompat_proved := torCompat_proved
  orbCompat := orbCompat
  orbCompat_proved := orbCompat_proved
  secCompat := secCompat
  secCompat_proved := secCompat_proved
  cusCompat := cusCompat
  cusCompat_proved := cusCompat_proved

/-- Actual bad-finiteness component. -/
theorem S2567badFinite_actual : NativeBadSetFinite X.S :=
  LeanFormal.IUT.N8Closure.NativeBadFintypeClosed.nativeBadSetFinite X

#check S2567NativeSourceAssembly
#check S2567badFinite_actual
#print axioms S2567NativeSourceAssembly
#print axioms S2567badFinite_actual
end LeanFormal.IUT.XiFPaper.S2567NativeSourceAssemblyConditionalActual
end