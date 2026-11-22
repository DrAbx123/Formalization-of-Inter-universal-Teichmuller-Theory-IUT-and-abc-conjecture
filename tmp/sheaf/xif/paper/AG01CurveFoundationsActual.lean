import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Scheme

/-!
# AG-01: smooth proper geometrically connected curves over a field
(component, not a paper object)

COMPONENT, not a paper object.  Named consumers: AG-02 genus interface,
coord/AG-INFRA-PLAN.md, [Mzk1] GeometricCore build.

Defines the curve predicate needed by [Mzk1] Theorem 2.5 using Mathlib's
existing scheme-morphism predicates (no axioms, no fakes):
* IsProper (Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:42),
* Smooth (Morphisms/Smooth.lean:62),
* SmoothOfRelativeDimension 1 (Morphisms/Smooth.lean:135) for dimension one,
* GeometricallyConnected (Geometrically/Connected.lean:40).
The structure is an honest data interface: an inhabitant is exactly a smooth
proper geometrically connected curve of relative dimension one over k.  The
sanity base case P1 (proper/smooth/geometrically connected of relative
dimension one) is the first target of the next AG batch (Mathlib has the
projective spectrum machinery, but the concrete P1 instance requires the Proj
construction; it is not assumed here).
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual

open AlgebraicGeometry CategoryTheory

universe u

/-- A smooth proper geometrically connected curve of relative dimension one
over a field k (the curve object of [Mzk1] Theorem 2.5). -/
structure S3133CurveOver (k : Type u) [Field k] where
  /-- the curve as a scheme over Spec k -/
  X : Over (Spec (CommRingCat.of k))
  /-- properness of the structure morphism -/
  proper : IsProper X.hom
  /-- smoothness -/
  smooth : Smooth X.hom
  /-- geometric connectedness -/
  geomConnected : GeometricallyConnected X.hom
  /-- relative dimension one -/
  relativeDimOne : SmoothOfRelativeDimension 1 X.hom

/-- The structure morphism is proper. -/
theorem S3133CurveOver_isProper {k : Type u} [Field k] (C : S3133CurveOver k) :
    IsProper C.X.hom :=
  C.proper

/-- The structure morphism is smooth. -/
theorem S3133CurveOver_isSmooth {k : Type u} [Field k] (C : S3133CurveOver k) :
    Smooth C.X.hom :=
  C.smooth

/-- The structure morphism is geometrically connected. -/
theorem S3133CurveOver_geometricallyConnected {k : Type u} [Field k]
    (C : S3133CurveOver k) :
    GeometricallyConnected C.X.hom :=
  C.geomConnected

/-- The structure morphism has relative dimension one. -/
theorem S3133CurveOver_relativeDimOne {k : Type u} [Field k]
    (C : S3133CurveOver k) :
    SmoothOfRelativeDimension 1 C.X.hom :=
  C.relativeDimOne

end LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual
