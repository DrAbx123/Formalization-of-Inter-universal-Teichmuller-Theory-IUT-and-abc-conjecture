import tmp.sheaf.xif.paper.PaperSourceGeometryActual
import tmp.sheaf.n8.closure.C3Roots

-- q-PARAMETER theta powers and independent mu_{2l} action.  These are NOT paper
-- theta values:
--
--   qParameter_j = q^(j^2), j = 1,...,l*;
--   paper theta uses the double-underline q_v = q^(1/2l): theta_j = q_v^(j^2).
--
-- The root-valued paper theta is in PaperC3ThetaRootActual / PaperC3RootThetaHullActual.
-- mu_{2l} is a separate multiplication by a 2l-torsion root of unity here.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperC3ThetaValuesActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

-- The actual algebraic closure where roots of unity and q powers live.
abbrev ThetaExtension (v : V) : Type u :=
  AlgebraicClosure (CommonPrimeCompletion (G.place v))

-- Direct paper theta value q^(j^2), no root extraction.
noncomputable def paperQParameterThetaValue
    (j : SignedLabel l.value) (v : V) : ThetaExtension (G := G) v :=
  (unitToAlgClosed (G.qUnit v) : ThetaExtension (G := G) v) ^
    ((gaussExponent j.1).toNat)

theorem paperQParameterThetaValue_eq_q_pow
    (j : SignedLabel l.value) (v : V) :
    paperQParameterThetaValue (G := G) j v =
      (unitToAlgClosed (G.qUnit v) : ThetaExtension (G := G) v) ^
        ((gaussExponent j.1).toNat) := rfl

-- An independent 2l-torsion root of unity at each place.
structure Mu2lRoot (v : V) where
  zeta : ThetaExtension (G := G) v
  zeta_pow : zeta ^ (2 * l.value) = 1

-- The independent mu_{2l} action: multiplication by zeta^m.
noncomputable def mu2lAction
    (R : Mu2lRoot (G := G) v) (m : Nat)
    (x : ThetaExtension (G := G) v) : ThetaExtension (G := G) v :=
  R.zeta ^ m * x

theorem mu2lAction_zero
    (R : Mu2lRoot (G := G) v) (x : ThetaExtension (G := G) v) :
    mu2lAction (G := G) R 0 x = x := by
  simp [mu2lAction]

theorem mu2lAction_add
    (R : Mu2lRoot (G := G) v) (m n : Nat)
    (x : ThetaExtension (G := G) v) :
    mu2lAction (G := G) R (m + n) x =
      mu2lAction (G := G) R m (mu2lAction (G := G) R n x) := by
  simp [mu2lAction, pow_add, mul_assoc]

theorem mu2lAction_period
    (R : Mu2lRoot (G := G) v) (x : ThetaExtension (G := G) v) :
    mu2lAction (G := G) R (2 * l.value) x = x := by
  simp [mu2lAction, R.zeta_pow]

-- Actual theta/mu orbit at each place.
noncomputable def paperQParameterMu2lOrbit
    (R : Mu2lRoot (G := G) v) (j : SignedLabel l.value) :
    Set (ThetaExtension (G := G) v) :=
  Set.range (fun m : Nat => mu2lAction (G := G) R m
    (paperQParameterThetaValue (G := G) j v))

-- Exact missing primitive-root API: a Mu2lRoot with exact order 2l.  The
-- action above is meaningful for any 2l-torsion root; primitivity is a
-- separate exact obligation, not faked by a choice.
structure PrimitiveMu2lRoot (v : V) extends Mu2lRoot (G := G) v where
  primitive_order :
    ∀ m : Nat, 0 < m -> m < 2 * l.value -> zeta ^ m ≠ 1

def PrimitiveMu2lRootRequired (v : V) : Prop :=
  Nonempty (PrimitiveMu2lRoot (G := G) v)

#check paperQParameterThetaValue
#check paperQParameterThetaValue_eq_q_pow
#check Mu2lRoot
#check mu2lAction
#check mu2lAction_zero
#check mu2lAction_add
#check mu2lAction_period
#check paperQParameterMu2lOrbit
#check PrimitiveMu2lRoot

end LeanFormal.IUT.XiFPaper.PaperC3ThetaValuesActual

end