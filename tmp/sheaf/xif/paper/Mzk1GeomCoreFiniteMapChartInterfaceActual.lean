import tmp.sheaf.xif.paper.Mzk1GeometricCoreRealStructureActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: finite-map construction gap (Lead A444/A445) -> ported flt_test FiniteMapData structure (Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean:19-55, 16 fields) + our route file constructor-from-fields (Mzk1GeomCoreFiniteMapRouteActual.finiteMapData_of_construction) -> TYPED CHART INTERFACE: FiniteMapChartData packages exactly the 16 fields; toFiniteMapData PROVED constructor; exact construction-gap text (no fake construction).

# Mzk1GeomCoreFiniteMapChartInterfaceActual — typed chart interface for the finite-map gap

WHAT IS PROVED:
* `FiniteMapChartData` mirrors the ported FiniteMapData fields exactly (U,V,f,g,m,
  affine/sup/mem_U/inf-basicOpen/transition/finiteness/levelSet_free);
* `toFiniteMapData`: the chart interface yields a `Mzk1FiniteMapData` (PROVED constructor);
* `coe_U_eq_compl`: the U-chart is the complement of the section range (PROVED from the
  interface field).
WHAT REMAINS NAMED (text, no free Prop): the actual construction of these 16 fields from
the function-field zero divisor: two affine charts around zeros/poles, the transition
relation, finiteness, and the level-set grading; no constructor/pullback API exists in
the ported trees or Mathlib.  Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

/-- Typed chart interface for the finite-map construction: exactly the 16 fields of the
ported FiniteMapData, packaged as data. -/
structure FiniteMapChartData (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) where
  U : C.Opens
  V : C.Opens
  f : Γ(C, U)
  g : Γ(C, V)
  m : ℕ
  isAffineOpen_U : IsAffineOpen U
  isAffineOpen_V : IsAffineOpen V
  sup_eq_top : U ⊔ V = ⊤
  mem_U_iff : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base
  inf_eq_basicOpen : U ⊓ V = C.basicOpen f
  inf_eq_basicOpen_g : U ⊓ V = C.basicOpen g
  res_f_mul_res_g :
    (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1
  finite_f : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite
  finite_g : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
    (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite
  levelSet_free : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
    Module.Finite S (S ⊗[R] Γ(C, U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
    Module.Free S (S ⊗[R] Γ(C, U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
    Module.finrank S (S ⊗[R] Γ(C, U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) = m

/-- **PROVED constructor:** the typed chart interface yields a ported finite map datum. -/
def FiniteMapChartData.toFiniteMapData (X : FiniteMapChartData c ε) :
    Mzk1FiniteMapData c ε :=
  { U := X.U
    V := X.V
    f := X.f
    g := X.g
    m := X.m
    isAffineOpen_U := X.isAffineOpen_U
    isAffineOpen_V := X.isAffineOpen_V
    sup_eq_top := X.sup_eq_top
    mem_U_iff := X.mem_U_iff
    inf_eq_basicOpen := X.inf_eq_basicOpen
    inf_eq_basicOpen_g := X.inf_eq_basicOpen_g
    res_f_mul_res_g := X.res_f_mul_res_g
    finite_f := X.finite_f
    finite_g := X.finite_g
    levelSet_free := X.levelSet_free }

/-- The U-chart is the complement of the section range (PROVED from the interface). -/
theorem FiniteMapChartData.coe_U_eq_compl (X : FiniteMapChartData c ε) :
    (X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ :=
  Set.ext fun x => X.mem_U_iff x

/-- The finite map degree is the interface degree (PROVED by definition). -/
theorem FiniteMapChartData.toFiniteMapData_m (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m := rfl

/-- Exact text record of the construction gap (the fields a construction must build). -/
def finiteMapChartGapText : List String :=
  [ "GAP: construct U (complement of the section range) and V (chart around the poles) as affine opens",
    "GAP: construct sections f on U and g on V from the function-field zero divisor, with inf_eq_basicOpen/inf_eq_basicOpen_g and res_f_mul_res_g",
    "GAP: prove finite_f/finite_g (module-finiteness over Polynomial R via algebraOfHom)",
    "GAP: prove levelSet_free (graded finite/free/rank-m level sets)",
    "NO API: no constructor of FiniteMapData from a function field exists in the ported trees; Mathlib has no projective-scheme morphism API" ]

/-- Chart interface rows: interface/proved vs construction gaps. -/
def finiteMapChartRows : List (String × String × String) :=
  [ ("typed 16-field chart interface", "DEFINED", "FiniteMapChartData")
  , ("chart interface => ported FiniteMapData", "PROVED", "FiniteMapChartData.toFiniteMapData")
  , ("U = complement of section range", "PROVED", "FiniteMapChartData.coe_U_eq_compl")
  , ("degree identity m = interface m", "PROVED", "FiniteMapChartData.toFiniteMapData_m")
  , ("construction of the 16 fields from the function field", "NAMED GAP", "text in finiteMapChartGapText: charts/transition/finiteness/level-set grading; no constructor API") ]

theorem finiteMapChartRows_length : finiteMapChartRows.length = 5 := rfl

#check FiniteMapChartData
#check FiniteMapChartData.toFiniteMapData
#check FiniteMapChartData.coe_U_eq_compl
#check finiteMapChartGapText
#check finiteMapChartRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual
end