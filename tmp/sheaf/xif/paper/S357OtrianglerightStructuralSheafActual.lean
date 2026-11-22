import Iut.Foundations.Frobenioid
import tmp.sheaf.xif.paper.S346OrbifoldStructuralSheafActual

/-! # S357: O^tri(T_x) structural sheaf condition on existing Frobenioid data

Repo candidate structures (actual, already defined):

* Iut.PreFrobenioid.LinearBaseIdentityEndomorphism A:
  the object monoid O^triangle(A) of Frobenioids I, Proposition 2.2.
* Units of that monoid: the O^times(A) unit factor.
* Iut.PreFrobenioid.CharacteristicSplitting.tau:
  the characteristic submonoid tau(A) in the split
  O^times(A) x tau(A) ~= O^triangle(A).
* Iut.SplitFrobenioidPresentation:
  a Frobenioid together with rational monoid transport, splitting index and
  characteristic splittings (IUT I Examples 3.2-3.4).

No existing definition of O^triangleright(T_x) / O^tri(T_x) as a positive
submonoid of the structural sheaf, and no actual bad-place split Frobenioid
instance for the native source, is present.

This file records the exact missing definition over the existing carrier:
an O^tri submonoid of the units of O^triangle(A), a q-section and a root
section with the 2l-th-power relation, plus the structural-sheaf condition.
No inhabitant/carrier/root is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S357OtrianglerightStructuralSheafActual

universe u

variable {l : PrimeGeFive}

open LeanFormal.IUT.XiFPaper.S346OrbifoldStructuralSheafActual

/-- Candidate O^tri carrier on an actual split Frobenioid presentation.

The carrier is the existing object monoid O^triangle(A) at an object A of the
split Frobenioid, restricted to a submonoid of its units.  The definition of
that submonoid (the paper's positivity/log-shell condition) is exactly the
missing structural-sheaf condition. -/
structure OtrianglerightOnSplitFrobenioid
    (S : Iut.SplitFrobenioidPresentation.{u}) where
  baseObject : S.frobenioid.carrier
  Otri : Submonoid
    (Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism baseObject))
  qSection : Otri
  rootSection : Otri
  root_pow : rootSection ^ (2 * l.value) = qSection
  structuralSheafCondition : Prop

/-- Exact missing O^tri structural-sheaf object over a split Frobenioid. -/
def OtrianglerightStructuralSheafRequired
    (S : Iut.SplitFrobenioidPresentation.{u}) : Prop :=
  Nonempty (OtrianglerightOnSplitFrobenioid (l := l) S)

/-- The existing O^triangle object monoid, named for alignment. -/
abbrev OtriangleMonoid
    {C D : Type u} [CategoryTheory.Category.{u} C]
    [CategoryTheory.Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) -> Prop}
    (P : Iut.PreFrobenioid C D IsFSM) (A : C) : Type u :=
  P.LinearBaseIdentityEndomorphism A

/-- The existing O^times unit factor of O^triangle(A). -/
abbrev OtimesUnits
    {C D : Type u} [CategoryTheory.Category.{u} C]
    [CategoryTheory.Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) -> Prop}
    (P : Iut.PreFrobenioid C D IsFSM) (A : C) : Type u :=
  Units (OtriangleMonoid P A)


end LeanFormal.IUT.XiFPaper.S357OtrianglerightStructuralSheafActual

end
