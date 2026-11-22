/-! DEPRECATED: the six-slot corrected torsion path is
`tmp.sheaf.xif.paper.NativeSourceTorsionGapsActualConstruction` with carrier
`rootsOfUnity 6` and the primitive-root label. This legacy module uses the old
l-torsion label domain and is not imported by the corrected path. -/

import tmp.sheaf.xif.paper.NativeSourceAssemblyActual
import tmp.sheaf.n8.closure.NativeSourceTorsionActual
import tmp.sheaf.n8.closure.NativeTorsionLabelProof

/-!
# Actual native torsion data and the exact NativeSourceTorsionGaps gap

For the native source assembly, the actual torsion data available from
clause (c) are:
* the actual l-torsion carrier Multiplicative (A.curve.LTorsion l);
* the actual rank-two torsion basis (Fin 2 -> ZMod l) = LTorsion l;
* the actual 6-torsion rationality statement;
* the actual canonical Galois representation into GL_2(ZMod l).

The NativeSourceTorsionGaps fields themselves are not constructed by the
source: clause (c) does not supply a map LTorsion -> Fin 6, a six-torsion
independence proposition/proof, or a q-parameter/l-torsion compatibility
proposition/proof. This file packages the actual objects and constructs the
full gap record only from those exact missing primitives. No arbitrary
label/proposition/axiom/sorry. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.InitialThetaSource.NativeTorsionGapsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceTorsion
open LeanFormal.IUT.Theorem311Source

universe u

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}

variable (D : SourceClauseC A S C B)

/-- Actual native torsion carrier. -/
abbrev actualTorsionCarrier : Type u :=
  nativeTorsionCarrier (A := A) (l := l)

/-- Actual clause-(c) rank-two torsion basis. -/
noncomputable def actualTorsionBasis :
    (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l :=
  D.torsion_basis

/-- Actual clause-(c) 6-torsion rationality. -/
theorem actualTorsion23Rational :
    PuncturedEllipticCurve.Torsion23Rational A.curve :=
  D.torsion23_rational

/-- Actual clause-(c) canonical Galois representation. -/
noncomputable def actualRepresentation :
    (AlgebraicClosure A.F ≃ₐ[A.F] AlgebraicClosure A.F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  D.galois_representation

/-- The actual source torsion objects packaged together. -/
structure ActualNativeTorsionObjects where
  carrier : Type u
  carrierGroup : Group carrier
  basis : (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l
  torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve
  representation :
    (AlgebraicClosure A.F ≃ₐ[A.F] AlgebraicClosure A.F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)

/-- The actual objects, constructed from clause (c). -/
noncomputable def actualNativeTorsionObjects :
    ActualNativeTorsionObjects (A := A) (l := l) D where
  carrier := actualTorsionCarrier (A := A) (l := l)
  carrierGroup := inferInstance
  basis := actualTorsionBasis (A := A) (l := l) D
  torsion23Rational := actualTorsion23Rational (A := A) (l := l) D
  representation := actualRepresentation (A := A) (l := l) D

/-- The full NativeSourceTorsionGaps record, constructed only from the exact
/-- missing source torsion primitives. -/
noncomputable def nativeSourceTorsionGaps
    (torsionLabel : actualTorsionCarrier (A := A) (l := l) -> Fin 6)
    (sixTorsionIndependent : Prop)
    (sixTorsionIndependent_proved : sixTorsionIndependent)
    (lTorsionCompatible : Prop)
    (lTorsionCompatible_proved : lTorsionCompatible) :
    NativeSourceTorsionGaps D where
  torsionLabel := torsionLabel
  sixTorsionIndependent := sixTorsionIndependent
  sixTorsionIndependent_proved := sixTorsionIndependent_proved
  lTorsionCompatible := lTorsionCompatible
  lTorsionCompatible_proved := lTorsionCompatible_proved

/-- The exact missing source torsion object for NativeSourceAssemblyFields. -/
structure MissingNativeTorsionGaps where
  torsionLabel : actualTorsionCarrier (A := A) (l := l) -> Fin 6
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  lTorsionCompatible : Prop
  lTorsionCompatible_proved : lTorsionCompatible

/-- The missing object is exactly NativeSourceTorsionGaps. -/
def MissingNativeTorsionGaps.toGaps
    (M : MissingNativeTorsionGaps (A := A) (l := l) D) :
    NativeSourceTorsionGaps D :=
  nativeSourceTorsionGaps (A := A) (l := l) D
    M.torsionLabel M.sixTorsionIndependent M.sixTorsionIndependent_proved
    M.lTorsionCompatible M.lTorsionCompatible_proved

#check actualTorsionCarrier
#check actualTorsionBasis
#check actualTorsion23Rational
#check actualRepresentation
#check actualNativeTorsionObjects
#check nativeSourceTorsionGaps
#check MissingNativeTorsionGaps
#check MissingNativeTorsionGaps.toGaps

end LeanFormal.IUT.InitialThetaSource.NativeTorsionGapsActual

end
