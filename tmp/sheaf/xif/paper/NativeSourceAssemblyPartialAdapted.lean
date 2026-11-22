import tmp.sheaf.xif.paper.NativeAssemblyCompatActualAdapted
import tmp.sheaf.xif.paper.NativeSourceAssemblyFieldsActual
import tmp.sheaf.xif.paper.NativeBadSetFiniteActual
import tmp.sheaf.xif.paper.ExactSequenceSplittingActualAdapted
import tmp.sheaf.n8.closure.NativeSourceAssembly
import tmp.sheaf.n8.closure.NativeReductionFieldsActual

/-!
# Partial NativeSourceAssembly from actual fields

Assembles the actual part of NativeSourceAssembly for a native input X:
* actual badFinite from the closed source-finiteness theorem;
* actual curve/puncturedCurve/cover/structureGroup and point maps;
* actual five compatibility fields;
* actual l-torsion carrier and rank-two basis (torsion partial).

The exact missing fields are split, torsionGaps, the exact-sequence
splitting section (exactSequence conditional), cuspCount/positivity, d7, and
cuspHyp. The full NativeSourceAssembly object is constructed only from those
exact missing fields. No arbitrary data/axiom/sorry. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeSourceAssemblyPartialAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.XiFPaper.NativeAssemblyCompatActualAdapted
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyFieldsActual
open LeanFormal.IUT.XiFPaper.NativeBadSetFiniteActual
open LeanFormal.IUT.XiFPaper.ExactSequenceSplittingActualAdapted

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The actual part of the assembly, constructed unconditionally. -/
structure ActualNativeAssemblyPart where
  badFinite : NativeBadSetFinite X.S
  carriers : ActualNativeAssemblyCarrierFields (l := l) X.S
  compat : ActualNativeAssemblyCompatFields (l := l) X.S
  torsionCarrier : Type u
  torsionBasis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      X.S.arithmetic.curve.LTorsion l

/-- The actual part, constructed from clause A-C/D/E data. -/
noncomputable def actualNativeAssemblyPart :
    ActualNativeAssemblyPart (l := l) X where
  badFinite := nativeBadSetFiniteField (X := X)
  carriers := actualNativeAssemblyCarrierFields (T := X.S)
  compat := actualNativeAssemblyCompatFields (T := X.S)
  torsionCarrier := Multiplicative (X.S.arithmetic.curve.LTorsion l)
  torsionBasis := X.S.clauseC.torsion_basis

/-- The exact missing fields of the assembly. -/
structure NativeSourceAssemblyMissingFields where
  split : NativeSplitMultiplicativeAtLift X.S
  torsionGaps : NativeSourceTorsionGaps (A := X.S.arithmetic)
    (S := X.S.tuple.source) (C := X.S.clauseA) (B := X.S.clauseB) X.S.clauseC
  section : ExactSequenceSplittingSection (l := l) X.S
  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount
  d7 : NativeD7Intake (SourceCompletion.ofSourceNative X.S)
  cuspHyp : NativeCuspClauseHypotheses

/-- Full assembly from the actual part plus the exact missing fields. -/
noncomputable def nativeSourceAssemblyOfMissing
    (M : NativeSourceAssemblyMissingFields (l := l) X) :
    NativeSourceAssembly X.S where
  badFinite := nativeBadSetFiniteField (X := X)
  split := M.split
  torsionGaps := M.torsionGaps
  exactSequence := sourceExactSequence_of_section (T := X.S) M.section
  curve := (actualNativeAssemblyCarrierFields (T := X.S)).curve
  puncturedCurve := (actualNativeAssemblyCarrierFields (T := X.S)).puncturedCurve
  cover := (actualNativeAssemblyCarrierFields (T := X.S)).cover
  structureGroup := (actualNativeAssemblyCarrierFields (T := X.S)).structureGroup
  structureGroupLaw := (actualNativeAssemblyCarrierFields (T := X.S)).structureGroupLaw
  curveToPunctured := (actualNativeAssemblyCarrierFields (T := X.S)).curveToPunctured
  coverToPunctured := (actualNativeAssemblyCarrierFields (T := X.S)).coverToPunctured
  cover_surjective := (actualNativeAssemblyCarrierFields (T := X.S)).cover_surjective
  cuspCount := M.cuspCount
  cuspCount_pos := M.cuspCount_pos
  d7 := M.d7
  cuspHyp := M.cuspHyp
  redCompat := (actualNativeAssemblyCompatFields (T := X.S)).redCompat
  redCompat_proved := (actualNativeAssemblyCompatFields (T := X.S)).redCompat_proved
  torCompat := (actualNativeAssemblyCompatFields (T := X.S)).torCompat
  torCompat_proved := (actualNativeAssemblyCompatFields (T := X.S)).torCompat_proved
  orbCompat := (actualNativeAssemblyCompatFields (T := X.S)).orbCompat
  orbCompat_proved := (actualNativeAssemblyCompatFields (T := X.S)).orbCompat_proved
  secCompat := (actualNativeAssemblyCompatFields (T := X.S)).secCompat
  secCompat_proved := (actualNativeAssemblyCompatFields (T := X.S)).secCompat_proved
  cusCompat := (actualNativeAssemblyCompatFields (T := X.S)).cusCompat
  cusCompat_proved := (actualNativeAssemblyCompatFields (T := X.S)).cusCompat_proved

#check ActualNativeAssemblyPart
#check actualNativeAssemblyPart
#check NativeSourceAssemblyMissingFields
#check nativeSourceAssemblyOfMissing

end LeanFormal.IUT.XiFPaper.NativeSourceAssemblyPartialAdapted

end
