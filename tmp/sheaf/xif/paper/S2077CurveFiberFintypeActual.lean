import tmp.sheaf.xif.paper.S2049CurveEtaleCardActual
import LeanFormal.IUT.Foundations.Geometry.CurveEtaleFundamentalGroup
import Mathlib.CategoryTheory.FintypeCat

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2077CurveFiberFintypeActual
open LeanFormal.IUT.Foundations.Geometry
open CategoryTheory AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {Omega : Type u} [Field Omega]
variable (x : Spec (CommRingCat.of Omega) ⟶ X)

/-- Conditional FintypeCat-valued geometric fiber functor, from a Fintype
instance on every geometric fiber. -/
noncomputable def S2077FiberFunctorFintype
    (hfin : ∀ Y : FiniteEtaleCover X, Fintype (geometricFiberObject Omega x Y)) :
    FiniteEtaleCover X ⥤ FintypeCat.{u} where
  obj Y := FintypeCat.of (geometricFiberObject Omega x Y)
  map f := FintypeCat.homMk (fun s => geometricFiberMap (Omega := Omega) (x := x) f s)
  map_id Y := (FintypeCat.homMk_eq_id_iff _).mpr (by funext s; rfl)
  map_comp f g := (FintypeCat.homMk_eq_comp_iff _ _ _).mpr (by funext s; rfl)

/-- Exact missing: finiteness of the geometric fiber for every finite etale
cover (the FintypeCat fiber input). -/
structure S2077FiberFiniteRequired where
  finite : ∀ Y : FiniteEtaleCover X, Finite (geometricFiberObject Omega x Y)

/-- Exact missing: a ProfiniteGrp structure on the actual fiber-functor
automorphism group, with a group equivalence to the ordinary Aut group. -/
structure S2077ProfiniteAutRequired where
  profinite : ProfiniteGrp.{u}
  autEquiv : curveEtaleFundamentalGroup Omega x ≃* profinite


/-- The FintypeCat fiber functor is compatible with the Type-valued geometric
fiber functor through FintypeCat.incl. -/
theorem S2077_incl_comp
    (hfin : ∀ Y : FiniteEtaleCover X, Fintype (geometricFiberObject Omega x Y)) :
    S2077FiberFunctorFintype x hfin ⋙ FintypeCat.incl = geometricFiberFunctor Omega x := rfl

end LeanFormal.IUT.XiFPaper.S2077CurveFiberFintypeActual
end