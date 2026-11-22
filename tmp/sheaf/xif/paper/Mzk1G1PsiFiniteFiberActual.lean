import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Tactic

/-!
# Finite fibers give finite point-preimages (adapter for B1 6(iii))

The set-theoretic preimage of a point under a morphism with finite fibre is finite.  This
packages the pattern used inside Mathlib (QuasiFinite.lean:172):
the fibre inclusion range_fiberι identifies the underlying point preimage with the range of
the map from the fibre scheme.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiniteFiberActual

variable {X Y : Scheme} (f : X ⟶ Y)

/-- If the scheme-theoretic fibre over y is finite, then the set-theoretic preimage of y is
finite. -/
theorem finite_preimage_singleton (y : Y) [Finite (f.fiber y)] :
    (f.base ⁻¹' {y}).Finite := by
  have h : (Set.univ : Set (f.fiber y)).Finite := Set.finite_univ
  have him := h.image (f.fiberι y).base
  simpa [Scheme.Hom.range_fiberι] using him

/-- If the scheme-theoretic fibres over a finite set B are finite, then the preimage of B is
finite. -/
theorem finite_preimage_finset (B : Finset Y) (h : ∀ y ∈ B, Finite (f.fiber y)) :
    (f.base ⁻¹' (B : Set Y)).Finite := by
  have hunion : (f.base ⁻¹' (B : Set Y)) = ⋃ y ∈ B, f.base ⁻¹' ({y} : Set Y) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_coe, Set.mem_singleton_iff]
    exact ⟨fun hx => ⟨f x, hx, rfl⟩, fun ⟨y, hy, hxy⟩ => hxy ▸ hy⟩
  rw [hunion]
  exact Set.Finite.biUnion B.finite_toSet fun y hy => by
    haveI := h y hy
    exact finite_preimage_singleton f y

/- NOTE: the IsFinite version is obtained by providing the instance
   Finite (f.fiber y) from the finite-morphism theory (Mathlib Fiber.lean:
   finite morphisms have discrete fibers; ZariskisMainTheorem.lean:410 shows the pattern
   Finite (f.fiber (f x)) via fiberHomeo.finite_iff). -/

#print axioms finite_preimage_singleton
#print axioms finite_preimage_finset
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiniteFiberActual
