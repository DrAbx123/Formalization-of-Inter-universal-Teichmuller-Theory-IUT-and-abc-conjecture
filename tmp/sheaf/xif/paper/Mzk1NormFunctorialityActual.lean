/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormDeterminantToolsActual
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic

/-! # P5-D / (C18): norm functoriality — restriction of scalars and norm transitivity -/

/-
| field | value |
|---|---|
| Status | green attempt: (C18) restriction-of-scalars determinant identity and relative norm transitivity (Mathlib re-exports) |
| Reuse | Mathlib `LinearMap.det_restrictScalars`（`RingTheory/Norm/Transitivity.lean:180-182`）；`Algebra.norm_norm`（`:202-205`）；`Mzk1NormDeterminantToolsActual`（C15/C16/C13 green） |
| GAP | project-level restriction-of-scalars instantiation (relative completion / initial theta data) still GAP-NORM-TRANS |
| 纪律 | no sorry/axiom; no new assumptions |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NormFunctorialityActual

/-- **(C18), restriction of scalars.**  For a tower `R ⊆ S` acting on `A`, the determinant
over `R` of the restriction of scalars of an `S`-linear endomorphism is the `R`-norm of its
`S`-determinant.  Re-export of Mathlib `LinearMap.det_restrictScalars`
(`Mathlib/RingTheory/Norm/Transitivity.lean:180`). -/
theorem det_restrictScalars_eq_norm_det
    {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [AddCommGroup A]
    [Module R A] [Module S A] [IsScalarTower R S A] [Module.Free S A]
    (f : A →ₗ[S] A) :
    LinearMap.det (f.restrictScalars R) = Algebra.norm R (LinearMap.det f) :=
  LinearMap.det_restrictScalars (f := f)

/-- **(C18), norm transitivity.**  `N_{A/R} = N_{S/R} ∘ N_{A/S}` for a tower of finite free
rings.  Re-export of Mathlib `Algebra.norm_norm` (`RingTheory/Norm/Transitivity.lean:202`). -/
theorem norm_norm_rel
    {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Ring A]
    [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Module.Free S A]
    (a : A) :
    Algebra.norm R (Algebra.norm S a) = Algebra.norm R a :=
  Algebra.norm_norm (a := a)

def normFunctorialityRows : List (String × String) :=
  [ ("det_restrictScalars_eq_norm_det", "(C18) det(restrictScalars f) = norm(det f) (re-export Transitivity:180)") ,
    ("norm_norm_rel", "(C18) norm_norm transitivity (re-export Transitivity:202)") ,
    ("GAP-NORM-TRANS", "project-level restriction-of-scalars instantiation remains") ]

theorem normFunctorialityRows_length : normFunctorialityRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1NormFunctorialityActual