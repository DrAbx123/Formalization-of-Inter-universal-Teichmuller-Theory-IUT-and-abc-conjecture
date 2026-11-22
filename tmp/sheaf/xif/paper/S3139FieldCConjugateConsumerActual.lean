import tmp.sheaf.xif.paper.S3139FieldCConjugateActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: field (C) consumer — finite-place conjugate channel readouts

Consumer interface for the finite-place channel of the copy action: given the
exact missing conjugate datum `SourceConjugateLocalUnitMap` (a conjugate map
`F_mod^x -> Pi`), the actual local Frobenius action on the value-monoid fibers
and its realified degree readout are exposed for the log-volume computation and
the lattice/mainline consumers (IUT III:616-620, Fig. I.5).

**Component, not paper object.**  Named consumers: the log-volume comparison
(`SourceConjugateLocalUnitMap.conjugateValue`) and the lattice/mainline
q/Theta readouts.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FieldCConjugateConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3139FieldCConjugateActual

universe uv upi umon u

variable {V : Type uv}

/-- The realified scalar readout of the conjugate local Frobenius action at one
fiber: the additive real degree of the acted-on value.  This is the quantity
the log-volume computation consumes. -/
def sourceConjugateRealReadout
    {F : FPrimeStrip.{umon, uv, upi} V} {G : Type u} [Group G]
    (D : SourceConjugateLocalUnitMap F G) (c : G) (v : V) (x : F.Mon v) : ℝ :=
  Multiplicative.toAdd (D.conjugateValue c v x)

/-- The readout is the realified degree of the actual local Frobenius action. -/
theorem sourceConjugateRealReadout_eq
    {F : FPrimeStrip.{umon, uv, upi} V} {G : Type u} [Group G]
    (D : SourceConjugateLocalUnitMap F G) (c : G) (v : V) (x : F.Mon v) :
    sourceConjugateRealReadout D c v x =
      Multiplicative.toAdd (F.degree v ((D.conjugateAut c v) x)) := rfl

/-- The conjugate action composes: the product copy acts by the two actual
Frobenius actions in order (the group law consumed by the (Ind2) copy action). -/
theorem sourceConjugateRealReadout_mul
    {F : FPrimeStrip.{umon, uv, upi} V} {G : Type u} [Group G]
    (D : SourceConjugateLocalUnitMap F G) (c d : G) (v : V) (x : F.Mon v) :
    (D.conjugateAut (c * d) v) x = (D.conjugateAut c v) ((D.conjugateAut d v) x) :=
  D.conjugateAut_mul_apply c d v x

/-- The actual local Frobenius action is an automorphism of the value-monoid
fiber (exposed for the tensor-factor action). -/
def sourceConjugateFiberAut
    {F : FPrimeStrip.{umon, uv, upi} V} {G : Type u} [Group G]
    (D : SourceConjugateLocalUnitMap F G) (c : G) (v : V) :
    MulAut (F.Mon v) :=
  D.conjugateAut c v

end LeanFormal.IUT.XiFPaper.S3139FieldCConjugateConsumerActual

end
