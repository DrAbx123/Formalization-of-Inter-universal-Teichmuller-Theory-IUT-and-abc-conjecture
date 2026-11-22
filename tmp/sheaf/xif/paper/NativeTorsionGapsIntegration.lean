/-! DEPRECATED: the six-slot corrected torsion path is
`tmp.sheaf.xif.paper.NativeSourceTorsionGapsActualConstruction` with carrier
`rootsOfUnity 6` and the primitive-root label. This legacy module uses the old
l-torsion label domain and is not imported by the corrected path. -/

import tmp.sheaf.xif.paper.NativeTorsionGapsActual
import tmp.sheaf.xif.paper.NativeTorsionFieldsComplete
import tmp.sheaf.xif.paper.NativeSourceAssemblyPartial
import tmp.sheaf.n8.closure.NativeSourceTorsionActual

/-!
# Native torsion gaps integration

This file integrates the actual clause (c) torsion objects:

* carrier Multiplicative (A.curve.LTorsion l);
* rank-two torsion basis D.torsion_basis;
* torsion23_rational;
* canonical Galois representation;

with the exact missing fields of NativeSourceTorsionGaps:

* torsionLabel : Multiplicative (A.curve.LTorsion l) -> Fin 6;
* sixTorsionIndependent : Prop with proof;
* and lTorsionCompatible, which is actual for SourceInitialThetaData via
  NativeTorsionFieldsComplete.completeLTorsionCompatible, but is not connected
  to the native SourceClauseC D by any tree theorem. It is therefore kept as an
  explicit field here rather than silently identified.

The conditional integration record NativeTorsionGapsPartial builds
NativeSourceTorsionGaps when the exact fields are supplied. Consumer checks are
included at the end. No label, independence proposition, compatibility
proposition, toy data, axiom, or unfilled proof is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeTorsionGapsIntegration

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceTorsion
open LeanFormal.IUT.N8Closure.PaperDonorsConstructed2
open LeanFormal.IUT.XiFPaper.NativeTorsionGapsActual
open LeanFormal.IUT.XiFPaper.NativeTorsionFieldsComplete
open LeanFormal.IUT.Theorem311Source

universe u

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}
variable (D : SourceClauseC A S C B)

/-- Actual clause (c) torsion carrier. -/
abbrev integratedTorsionCarrier : Type u :=
  nativeTorsionCarrier (A := A) (l := l)

/-- Actual clause (c) rank-two torsion basis. -/
noncomputable def integratedTorsionBasis :
    (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l :=
  D.torsion_basis

/-- Actual clause (c) 6-torsion rationality. -/
theorem integratedTorsion23Rational :
    PuncturedEllipticCurve.Torsion23Rational A.curve :=
  D.torsion23_rational

/-- Actual clause (c) canonical Galois representation. -/
noncomputable def integratedTorsionRepresentation :
    (AlgebraicClosure A.F ≃ₐ[A.F] AlgebraicClosure A.F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  D.galois_representation

/-- Integration record: actual carrier/basis and the exact remaining
NativeSourceTorsionGaps fields. lTorsionCompatible is explicit because no tree
theorem passes from SourceInitialThetaData compatibility to this native D. -/
structure NativeTorsionGapsPartial where
  torsionLabel : integratedTorsionCarrier (l := l) -> Fin 6
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  lTorsionCompatible : Prop
  lTorsionCompatible_proved : lTorsionCompatible

/-- Conditional integration into NativeSourceTorsionGaps. -/
noncomputable def toNativeSourceTorsionGaps
    (G : NativeTorsionGapsPartial (l := l) D) :
    NativeSourceTorsionGaps D where
  torsionLabel := G.torsionLabel
  sixTorsionIndependent := G.sixTorsionIndependent
  sixTorsionIndependent_proved := G.sixTorsionIndependent_proved
  lTorsionCompatible := G.lTorsionCompatible
  lTorsionCompatible_proved := G.lTorsionCompatible_proved

/-- The integrated actual carrier is the clause (c) l-torsion carrier. -/
theorem integratedTorsionCarrier_eq :
    integratedTorsionCarrier (l := l) =
      nativeTorsionCarrier (A := A) (l := l) := rfl

/-- Exact missing integration fields: label and six-torsion independence, plus
the native-D compatibility proposition (actual for SourceInitialThetaData but
not connected to D in the tree). -/
def MissingTorsionGapsIntegration : Prop :=
  Nonempty (NativeTorsionGapsPartial (l := l) D)

/-- Consumer check: the assembly missing-field package consumes torsionGaps. -/
#check LeanFormal.IUT.XiFPaper.NativeSourceAssemblyPartial.NativeSourceAssemblyMissingFields
#check NativeSourceTorsionGaps
#check NativeSourceTorsionGaps.toSourceTorsionClause
#check toNativeSourceTorsionGaps
#check integratedTorsionBasis
#check integratedTorsion23Rational
#check integratedTorsionRepresentation
#check MissingTorsionGapsIntegration

end LeanFormal.IUT.XiFPaper.NativeTorsionGapsIntegration

end
