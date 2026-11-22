import LeanFormal.IUT.ABCBridge.Geometry.LegendreQuadraticParameterFields
import LeanFormal.IUT.IUTII.Kummer.AlgebraicClosureKummerRoots
import tmp.sheaf.xif.paper.Node09TateComparisonActual
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.AlgebraicClosure

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09TateRootFieldActual

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Actual quadratic extension containing sqrt(4x+1): the IntermediateField
sqrt(4x+1) inside the algebraic closure, with finite dimension ≤ 2. -/
theorem exists_quadratic_sqrt_field (x : K) :
    ∃ L : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K L ∧ Module.finrank K L ≤ 2 ∧
        ∃ s : L, s ^ 2 = algebraMap K L (4 * x + 1) := by
  let L : IntermediateField K (AlgebraicClosure K) :=
    LegendreQuadraticParameterFields.squareRootField K (4 * x + 1)
  have hfin : FiniteDimensional K L :=
    LegendreQuadraticParameterFields.squareRootField_finiteDimensional K (4 * x + 1)
  have hrank : Module.finrank K L ≤ 2 :=
    LegendreQuadraticParameterFields.squareRootField_finrank_le_two K (4 * x + 1)
  refine ⟨L, hfin, hrank, ?_⟩
  exact ⟨LegendreQuadraticParameterFields.squareRoot K (4 * x + 1),
    LegendreQuadraticParameterFields.squareRoot_sq K (4 * x + 1)⟩

/-- Root field of an actual (2l)-th root of q, built inside the algebraic closure. -/
theorem exists_twoL_root_field (l : PrimeGeFive) (q : K) (hq : q ≠ 0) :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (α : L),
      α ^ (2 * l.value) = algebraMap K L q := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) q) (by
      have h5 := l.ge_five
      omega : 0 < 2 * l.value)
  let L : IntermediateField K (AlgebraicClosure K) := IntermediateField.adjoin K {z}
  have hzL : z ∈ L := IntermediateField.mem_adjoin_simple_self K z
  refine ⟨L, ⟨z, hzL⟩, ?_⟩
  apply Subtype.ext
  exact hz

/-- Galois-fixed algebraic-closure roots descend to K (actual descent theorem). -/
theorem twoL_root_descends_of_fixed (l : PrimeGeFive) (q : K)
    (z : AlgebraicClosure K) (hz : z ^ (2 * l.value) = algebraMap K (AlgebraicClosure K) q)
    (hfixed : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ z = z) :
    ∃ r : K, algebraMap K (AlgebraicClosure K) r = z :=
  fixed_by_absoluteGalois_mem_base z hfixed

def Node09TateRootFieldStatus : List String :=
  [ "actual: exists_quadratic_sqrt_field builds the finite quadratic IntermediateField sqrt(4x+1) in the algebraic closure, with actual s and s^2=4x+1",
    "actual: exists_twoL_root_field builds the root field K(alpha) with alpha^(2l)=q inside the algebraic closure",
    "actual: twoL_root_descends_of_fixed uses the absolute-Galois fixed-point theorem to descend a fixed root to K",
    "BLOCKER root-to-K_v: the actual 2l-root is only in the algebraic closure; to place it in the specified K_v one needs the actual 2l-torsion rationality (every K_v-automorphism fixes alpha), which is not in the tree; without it hfixed cannot be proved",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateRootFieldActual