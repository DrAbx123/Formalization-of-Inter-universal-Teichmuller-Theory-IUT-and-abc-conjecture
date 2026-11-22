import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineGluedActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

set_option relaxedAutoImplicit false
noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1FiniteDisjointBelyiActual
open LeanFormal.IUT
open MvPolynomial AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective line `ℙ¹ = Proj ℚ[X₀, X₁]`. -/
noncomputable def projectiveLine : Scheme :=
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)

/-- The boundary value set `{0, 1, ∞} ⊂ ℙ¹`, realized as the zero locus of
the three homogeneous linear forms `X₀`, `X₁`, `X₀ - X₁`.  Over any field
this closed set consists exactly of the three points `[1:0]`, `[1:1]`,
`[0:1]`. -/
noncomputable def boundarySet : Set projectiveLine :=
  ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
    ({X 0, X 1, X 0 - X 1} : Set (MvPolynomial (Fin 2) ℚ))

/-- The boundary value set is a closed subset of `ℙ¹`. -/
theorem boundarySet_isClosed : IsClosed boundarySet :=
  ProjectiveSpectrum.isClosed_zeroLocus _ _

/-- The actual reduced boundary `E_i = φ_i⁻¹({0,1,∞})` of an actual scheme
morphism `φ_i : Y_n → ℙ¹` (route §7.1). -/
def boundaryPreimage (n : ℕ) (phi : fermatCurveScheme n ⟶ projectiveLine) :
    Set (fermatCurveScheme n) :=
  phi ⁻¹' boundarySet

/-- The B1 producer input of the section 7.1 recursion.

INTERFACE, NO INHABITANT: for every finite set of points T of Y_n there is an
actual morphism phi : Y_n -> P1 such that the boundary preimage
phi^{-1}({0,1,infinity}) avoids T.  The G-C lane supplies this from the B1
construction with protected set S = empty; the section 7.1 recursion then
produces r+1 maps with pairwise disjoint E_i by taking T to be the union of the
previously constructed boundaries. -/
def B1AvoidingMaps (n : ℕ) : Prop :=
  ∀ T : Finset (fermatCurveScheme n),
    ∃ phi : fermatCurveScheme n ⟶ projectiveLine,
      ∀ x ∈ T, x ∉ boundaryPreimage n phi

/-- The G-K finite family of the route §7.1: `r + 1` actual scheme morphisms
`φ_i : Y_n → ℙ¹` (`Y_n` the actual closed subscheme of `ℙ²`) whose reduced
boundaries `E_i = φ_i⁻¹({0,1,∞})` are pairwise disjoint.

NO INHABITANT YET: the inhabitant is produced by the section 7.1 recursion from
the G-C B1 maps (see B1AvoidingMaps); the field disjoint_edges is a required
condition, not an assumption used as a conclusion. -/
structure ActualDisjointBelyiFamily (n : ℕ) where
  /-- The number `r` of the route; there are `r + 1` maps. -/
  r : ℕ
  /-- The actual maps `φ_i : Y_n → ℙ¹`. -/
  phi : Fin (r + 1) → (fermatCurveScheme n ⟶ projectiveLine)
  /-- The boundaries `E_i` are pairwise disjoint, as in route (E1). -/
  disjoint_edges : Pairwise fun i j =>
    Disjoint (boundaryPreimage n (phi i)) (boundaryPreimage n (phi j))

/-- The existential form of the G-K family existence statement: with
`r = d · |V|`, the actual curve `Y_n` carries a family of `r + 1` actual
morphisms to `ℙ¹` with pairwise disjoint boundaries. -/
def HasActualDisjointBelyiFamily (n d : ℕ) (V : Finset ℕ) : Prop :=
  ∃ F : ActualDisjointBelyiFamily n, F.r = d * V.card

/-! ### The route 7.1 target: maps to the glued projective line -/

/-- The boundary value set {0,1,infinity} inside the glued P1: the images of
lambda = 0 and lambda = 1 in the lambda-chart and of t = 0 in the t-chart. -/
noncomputable def gluedBoundary : Set projectiveLineGlued :=
  Mzk1G1ProjectiveLineBoundaryActual.boundarySetGlued

/-- Our boundary set is the canonical one of the G-C lane, definitionally. -/
theorem gluedBoundary_eq : gluedBoundary =
    Mzk1G1ProjectiveLineBoundaryActual.boundarySetGlued := rfl


/-- The boundary preimage E = phi^{-1}({0,1,infinity}) for maps to the glued P1. -/
def gluedBoundaryPreimage (n : ℕ) (phi : fermatCurveScheme n ⟶ projectiveLineGlued) :
    Set (fermatCurveScheme n) :=
  phi ⁻¹' gluedBoundary

/-- The boundary preimage is the canonical one of the G-C lane. -/
theorem gluedBoundaryPreimage_eq (n : ℕ)
    (phi : fermatCurveScheme n ⟶ projectiveLineGlued) :
    gluedBoundaryPreimage n phi =
      Mzk1G1ProjectiveLineBoundaryActual.boundaryPreimageGlued phi := rfl

/-- The G-K finite family of route section 7.1 in its final form: r + 1 actual
morphisms from the canonical glued Y_n to the glued P1 with pairwise disjoint
boundary preimages.

NO INHABITANT YET: produced by the section 7.1 recursion from the G-C B1 maps
(interface: for every finite set of points T of Y_n there is phi with
phi(T) disjoint from {0,1,infinity}); see B1AvoidingMaps.  The field
disjoint_edges is a required condition, not an assumption used as a conclusion. -/
structure GluedBelyiFamily (n : ℕ) where
  r : ℕ
  phi : Fin (r + 1) → (fermatCurveScheme n ⟶ projectiveLineGlued)
  disjoint_edges : Pairwise fun i j =>
    Disjoint (gluedBoundaryPreimage n (phi i)) (gluedBoundaryPreimage n (phi j))

/-- The existential form on the glued P1: with r = d * |V| there are r+1 maps
with pairwise disjoint boundary preimages. -/
def HasGluedBelyiFamily (n d : ℕ) (V : Finset ℕ) : Prop :=
  ∃ F : GluedBelyiFamily n, F.r = d * V.card

#print axioms boundarySet_isClosed
end LeanFormal.IUT.XiFPaper.G1FiniteDisjointBelyiActual
end
