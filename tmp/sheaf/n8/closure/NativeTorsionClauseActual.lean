import tmp.sheaf.n8.closure.NativeContractFieldsActualAttempt
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction

/-!
# Native torsion clause attempt

Actual from native Clause C: SourceTorsionDatum l X.S.arithmetic.  Clause C
supplies the torsion basis, the SL2 image containment and the kernel-field
identification, which are exactly the three fields of SourceTorsionDatum.

Not actual: a full SourceTorsionClause.  The contract clause additionally
requires a Group-valued labelled six-torsion carrier with a map to Fin 6,
representation surjectivity (Clause C proves SL2 containment, not GL2
surjectivity), and the sixTorsionIndependent/lTorsionCompatible source cards.
No production declaration projects these from SourceNativeInitialThetaData.
D4D9Supply has a D5TorsionSupply field, but that is supplied source data, not
a native-S construction.  No arbitrary clause is assembled.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeTorsionClauseActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- Actual SourceTorsionDatum from native Clause C. -/
noncomputable def nativeTorsionDatum (X : N8NativeInput l) :
    SourceTorsionDatum l X.S.arithmetic where
  torsion_basis := X.S.clauseC.torsion_basis
  image_contains_SL2 := by
    rw [← X.S.clauseC.representation_eq_canonical]
    exact X.S.clauseC.image_contains_SL2
  kernel_field_identification := X.S.clauseC.kernel_field_identification

theorem nativeTorsionDatum_nonempty (X : N8NativeInput l) :
    Nonempty (SourceTorsionDatum l X.S.arithmetic) :=
  ⟨nativeTorsionDatum X⟩

/-- Exact target: a full SourceTorsionClause over the native arithmetic root. -/
def NativeTorsionClauseTarget (l : PrimeGeFive) : Prop :=
  Nonempty (SourceTorsionClause.{0, 0, 0} l)

/-- Exact missing production data for a full SourceTorsionClause.  These are
not filled; they are the declarations that would need to be produced. -/
structure NativeTorsionClauseGap where
  labelledSixTorsionCarrier : Prop
  representationSurjective : Prop
  sixTorsionIndependent : Prop
  lTorsionCompatible : Prop

end LeanFormal.IUT.N8Closure.NativeTorsionClauseActual
