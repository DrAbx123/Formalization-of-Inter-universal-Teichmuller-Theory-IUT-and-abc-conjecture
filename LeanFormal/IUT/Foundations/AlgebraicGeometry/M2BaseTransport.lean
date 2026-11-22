import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Base transport for fixed-point subalgebras

If `A` is an `R`-algebra and an `S`-algebra with `S → R → A`, then the
`R`-fixed-point subalgebra, restricted to `S`, is the `S`-fixed-point
subalgebra.  This supplies the per-corner `S`-algebra transport used by the
global atom assembly.
-/
namespace ABCBridge.M2BaseTransport

universe u v w x

variable {S : Type u} [CommRing S] {R : Type v} [CommRing R] {A : Type w} [CommRing A]
  [Algebra S R] [Algebra R A] [Algebra S A] [IsScalarTower S R A]
  {G : Type x} [Group G] [MulSemiringAction G A]
  [SMulCommClass G R A] [SMulCommClass G S A]

/-- Restricting the `R`-fixed points to `S` gives the `S`-fixed points. -/
theorem fixedPoints_subalgebra_restrictScalars :
    (FixedPoints.subalgebra R A G).restrictScalars S =
      FixedPoints.subalgebra S A G := by
  ext a
  rfl

/-- The identity comparison, as an `S`-algebra equivalence, between the
`S`-fixed points and the restriction of the `R`-fixed points. -/
noncomputable def fixedPoints_subalgebra_restrictScalars_algEquiv :
    FixedPoints.subalgebra S A G ≃ₐ[S]
      (FixedPoints.subalgebra R A G).restrictScalars S := by
  rw [fixedPoints_subalgebra_restrictScalars]

/-- If `R` is finite etale over `S` and the `R`-fixed points are finite etale
over `R`, then the `S`-fixed points are finite etale over `S`. -/
theorem fixedPoints_restrictScalars_finiteEtale
    [Algebra.Etale S R] [Module.Finite S R]
    (hEt : Algebra.Etale R (FixedPoints.subalgebra R A G))
    (hFin : Module.Finite R (FixedPoints.subalgebra R A G)) :
    Algebra.Etale S (FixedPoints.subalgebra S A G) ∧
      Module.Finite S (FixedPoints.subalgebra S A G) := by
  haveI : IsScalarTower S R (FixedPoints.subalgebra R A G) :=
    IsScalarTower.of_algebraMap_eq (fun s => by
      apply Subtype.ext
      simpa using (IsScalarTower.algebraMap_apply S R A s))
  have hEtS : Algebra.Etale S ((FixedPoints.subalgebra R A G).restrictScalars S) :=
    Algebra.Etale.comp (R := S) R (FixedPoints.subalgebra R A G)
  have hFinS : Module.Finite S ((FixedPoints.subalgebra R A G).restrictScalars S) :=
    Module.Finite.trans (R := S) R (FixedPoints.subalgebra R A G)
  haveI : Algebra.Etale S ((FixedPoints.subalgebra R A G).restrictScalars S) := hEtS
  haveI : Module.Finite S ((FixedPoints.subalgebra R A G).restrictScalars S) := hFinS
  refine ⟨?_, ?_⟩
  · exact Algebra.Etale.of_equiv
      (fixedPoints_subalgebra_restrictScalars_algEquiv (S := S) (R := R) (A := A) (G := G)).symm
  · exact Module.Finite.equiv
      (fixedPoints_subalgebra_restrictScalars_algEquiv (S := S) (R := R) (A := A) (G := G)).symm.toLinearEquiv

end ABCBridge.M2BaseTransport