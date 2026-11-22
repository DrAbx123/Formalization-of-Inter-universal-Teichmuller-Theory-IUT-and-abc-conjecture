import tmp.sheaf.xif.paper.S3133ValueGroupDegreeActual
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore

/-!
# Exact missing value-group homomorphism to a source prime-strip value monoid (component)

COMPONENT, not a paper object.  Named consumers: abc task-39 F4(a) value-group
splitting; degree-faithful value-group action.

Source: IUT II, Example 1.8, (ix) (value-group degree); [AbsTopIII],
Proposition 5.8, (ii) (realified degree / value-group compatibility); IUT III,
Remark 3.9.4 (log-volume and value-group compatibility).

STATUS: NO such psi exists in the tree.  The actual realified divisor group
S3133ValueGroupDegreeActual.GlobalDivisorMonoid has an actual degree homomorphism
globalDegree : GlobalDivisorMonoid →* Multiplicative Real (with the proved
readout globalDegree_realifiedPrimePower / _comp_primePowerHom), but there is no
constructed monoid homomorphism to any source prime-strip value monoid F.Mon v,
and no theorem identifying globalPrimeWeight/globalDegree with a source
value-monoid degree.  This file records the exact missing structure: due to this
file's parameterization it can be stated without choosing an OriginalInput
prime-strip (F is supplied by the consumer).

The Real-indexed generator side IS actual and citable: for every actual global
prime index v, globalPrimeWeight v ≠ 0 (S3133GlobalPrimeWeightActual), so
globalRealifiedPrimePowerHom v : Multiplicative Real →* GlobalDivisorMonoid is
degree-faithful unconditionally.

No field is inhabited; no sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133ValueGroupPsiMissingActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual

universe ua uv upi umon ui

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable {V : Type uv}

/-- Exact missing value-group homomorphism to a source prime-strip value monoid:
a monoid homomorphism from the actual realified divisor monoid to F.Mon v that
commutes with the degree readouts (globalDegree vs the source degree F.degree v),
together with the agreement with the positive-Real action on the normalized
Real-indexed generator.  No inhabitant is constructed. -/
structure S3133ValueGroupPsiMissing
    (F : FPrimeStrip.{umon, uv, upi} V) (v : V) where
  /-- the missing monoid homomorphism phi : realified divisor monoid ->* F.Mon v -/
  psi : GlobalDivisorMonoid (X := X) →* F.Mon v
  /-- exact degree-commutation proposition -/
  degree_comm : Prop
  degree_comm_eq :
    degree_comm = ∀ s : GlobalDivisorMonoid (X := X),
      globalDegree (X := X) s = F.degree v (psi s)
  /-- exact agreement with the positive-Real action on the normalized
  Real-indexed generator -/
  posRealAction_agreement : Prop

/-- The existence of the missing value-group homomorphism data. -/
def S3133ValueGroupPsiMissingData
    (F : FPrimeStrip.{umon, uv, upi} V) (v : V) : Prop :=
  Nonempty (S3133ValueGroupPsiMissing (l := l) X F v)

end LeanFormal.IUT.XiFPaper.S3133ValueGroupPsiMissingActual
