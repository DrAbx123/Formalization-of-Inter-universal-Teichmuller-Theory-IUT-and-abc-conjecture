/-
# S1957: the actual boundary cusp of the S1726 orbicurve, unconditional

This file is the assembly consumer of three already proved files.

* `S1946ChartAlgEquivActual`:
  - `S1946ChartAlgEquiv : S1937ChartAlgEquiv`, the F'-algebra chart identification
    `Away WGr Zbar ≃ₐ[S1726K] S1726CoordinateRing` (the first S1937 missing datum);
  - `S1946Compactification_of_domain (hdom : IsDomain W) : S1913AffineCompactification`,
    the S1937 scheme-level projective compactification datum of the actual affine model,
    with its chart input supplied and its density input derived from `IsDomain W`.

* `S1947DomainWActual`:
  - `S1947_isDomain_W : IsDomain W` **unconditionally** (the homogeneous Weierstrass
    polynomial `Wang` is Eisenstein at `(Z)`, hence irreducible, hence prime);
  - `S1947DenseChart : S1925DenseChart`, the S1937 density residual, now unconditional.

* `S1926RepresentableOpenImmersionActual`:
  - `S1926RepresentableOpenImmersion C : S1913RepresentableOpenImmersion C` for every
    compactification datum `C` (the second S1913 input, discharged from the actual
    schematic fibre product and S1911's two-pullback witness);
  - `S1926Cusp_of_compactification C : Nonempty (OrbicurveBoundaryCusp S1726Orbicurve)`.

## What is assembled here

```
S1957Compactification : S1913AffineCompactification
  := S1946Compactification_of_domain S1947_isDomain_W

S1957ActualCusp : Nonempty (OrbicurveBoundaryCusp S1726Orbicurve)
  := S1926Cusp_of_compactification S1957Compactification
```

Nothing is assumed and no datum is faked.

* The compactifying object is the projective closure `Proj WGr` of the affine Weierstrass
  model of S1726 with structure morphism `S1937ProjHom`; the two identification lemmas
  `S1957Compactification_scheme` and `S1957Compactification_pointAtInfinity` record that
  definitionally.  Its boundary point is `S1937BoundaryPoint = (0:1:0)`, and the open
  immersion, separation, density and properness fields are the S1937 proofs, not inputs.

* The cusp is S1913's `S1913Cusp_of_compactification` applied to that datum, with the
  representable-open-immersion input supplied by S1926's theorem
  (`S1957RepresentableOpenImmersion`).  No cusp witness, no compactification and no
  2-categorical input is postulated.

Consequently the D9 boundary cusp of the actual S1726 orbicurve is no longer conditional on
any missing scheme-level or 2-categorical datum, and the three former residuals
(`S1937ChartAlgEquiv`, `S1925DenseChart`, `S1913RepresentableOpenImmersion`) are all
discharged theorems.  The only axioms are the standard Lean/Mathlib ones
(`propext`, `Classical.choice`, `Quot.sound`), audited at the end of the file.
-/
import tmp.sheaf.xif.paper.S1946ChartAlgEquivActual
import tmp.sheaf.xif.paper.S1947DomainWActual
import tmp.sheaf.xif.paper.S1926RepresentableOpenImmersionActual

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1957ActualCuspActual

open CategoryTheory
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1925ProjectiveClosureActual
open LeanFormal.IUT.XiFPaper.S1937ProjectiveClosureGeometryActual
open LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual
open LeanFormal.IUT.XiFPaper.S1946ChartAlgEquivActual
open LeanFormal.IUT.XiFPaper.S1947DomainWActual
open LeanFormal.IUT.XiFPaper.S1926RepresentableOpenImmersionActual

/-! ## 1. The actual compactification, unconditionally

`S1946Compactification_of_domain` takes the single algebraic hypothesis `IsDomain W`.
S1947 proves that hypothesis unconditionally, so the S1937 scheme-level datum now exists
without hypotheses. -/

/-- **The actual compactification of the S1726 affine Weierstrass model**, unconditional:
S1946's scheme-level projective compactification with `hdom := S1947_isDomain_W`. -/
noncomputable def S1957Compactification : S1913AffineCompactification :=
  S1946Compactification_of_domain S1947_isDomain_W

/-- The compactification is exactly S1937's construction from the S1946 chart identification
and the S1947 density of the affine chart (definitional unfolding). -/
theorem S1957Compactification_eq_S1937 :
    S1957Compactification
      = S1937AffineCompactification S1946ChartAlgEquiv
          (S1937DenseChart_of_domain S1947_isDomain_W) := rfl

/-- The compactifying scheme is the projective closure `Proj WGr` of the affine model
(with the S1937 structure morphism). -/
theorem S1957Compactification_scheme :
    S1957Compactification.scheme = Over.mk S1937ProjHom := rfl

/-- The boundary point of the compactification is the point at infinity `O = (0:1:0)`. -/
theorem S1957Compactification_pointAtInfinity :
    S1957Compactification.pointAtInfinity = S1937BoundaryPoint := rfl

/-! ## 2. The S1947 density and the S1926 representable open immersion, at this datum -/

/-- The density residual of S1925/S1937, at the actual homogeneous coordinate ring. -/
theorem S1957DenseChart : S1925DenseChart :=
  S1947DenseChart

/-- **The second S1913 input is a theorem at the actual datum**: the stack map of the open
immersion of the projective closure is representably an open immersion. -/
theorem S1957RepresentableOpenImmersion :
    S1913RepresentableOpenImmersion S1957Compactification :=
  S1926RepresentableOpenImmersion S1957Compactification

/-! ## 3. The actual boundary cusp -/

/-- **The actual boundary cusp of the S1726 orbicurve is nonempty**, unconditional: S1926's
cusp construction applied to the actual compactification `S1957Compactification`. -/
theorem S1957ActualCusp : Nonempty (OrbicurveBoundaryCusp S1726Orbicurve) :=
  S1926Cusp_of_compactification S1957Compactification

/-- The cusp through S1913's two-input construction, with both inputs discharged: the
scheme-level datum is `S1957Compactification` and the representable open immersion is
`S1926OpenImmersion`. -/
theorem S1957ActualCusp_via_inputs :
    Nonempty (OrbicurveBoundaryCusp S1726Orbicurve) :=
  S1913Cusp_of_inputs S1957Compactification
    (S1926OpenImmersion S1957Compactification)

/-! ## 4. Target-locked checks -/

-- The three source theorems, at their exact frozen statements.
example : S1937ChartAlgEquiv := S1946ChartAlgEquiv
example : IsDomain W := S1947_isDomain_W
example : S1925DenseChart := S1947DenseChart
example : ∀ C : S1913AffineCompactification, S1913RepresentableOpenImmersion C :=
  S1926RepresentableOpenImmersion

-- The assembled objects, at their exact target types.
example : S1913AffineCompactification := S1957Compactification
example : S1913RepresentableOpenImmersion S1957Compactification :=
  S1957RepresentableOpenImmersion
example : Nonempty (OrbicurveBoundaryCusp S1726Orbicurve) := S1957ActualCusp

#check @S1946Compactification_of_domain
#check @S1947_isDomain_W
#check @S1926Cusp_of_compactification
#check @S1957Compactification
#check @S1957Compactification_eq_S1937
#check @S1957Compactification_scheme
#check @S1957Compactification_pointAtInfinity
#check @S1957RepresentableOpenImmersion
#check @S1957ActualCusp
#check @S1957ActualCusp_via_inputs

/-! ## 5. Axiom audit -/

#print axioms S1957Compactification
#print axioms S1957Compactification_eq_S1937
#print axioms S1957Compactification_scheme
#print axioms S1957Compactification_pointAtInfinity
#print axioms S1957DenseChart
#print axioms S1957RepresentableOpenImmersion
#print axioms S1957ActualCusp
#print axioms S1957ActualCusp_via_inputs

end LeanFormal.IUT.XiFPaper.S1957ActualCuspActual
