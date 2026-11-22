import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveEtaleCovers
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

noncomputable section
open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace Scratch

universe u

structure ConnectedEtaleAlgebra (K : Type u) [Field K] where
  L : Type u
  [field : Field L]
  [algebra : Algebra K L]
  [finite : Module.Finite K L]
  [etale : Algebra.Etale K L]
  finrank_eq_two : Module.finrank K L = 2

attribute [instance] ConnectedEtaleAlgebra.field ConnectedEtaleAlgebra.algebra
  ConnectedEtaleAlgebra.finite ConnectedEtaleAlgebra.etale

def Qpoly (K : Type u) [Field K] (d : K) : Polynomial K :=
  Polynomial.X ^ 2 - Polynomial.C d

theorem Qpoly_irred (K : Type u) [Field K] (d : K) (hd : ¬ IsSquare d) :
    Irreducible (Qpoly K d) := by
  rw [Qpoly]
  refine X_pow_sub_C_irreducible_of_prime (p := 2) (by norm_num) ?_
  intro b hb
  exact hd ⟨b, by rw [pow_two] at hb; exact hb.symm⟩

def ofNonsquare (K : Type u) [Field K] [CharZero K] (d : K) (hd : ¬ IsSquare d) :
    ConnectedEtaleAlgebra K where
  L := AdjoinRoot (Qpoly K d)
  field := by
    letI : Fact (Irreducible (Qpoly K d)) := ⟨Qpoly_irred K d hd⟩
    infer_instance
  algebra := inferInstance
  finite := by
    change Module.Finite K (AdjoinRoot (Qpoly K d))
    exact (Polynomial.monic_X_pow_sub_C d (by norm_num : 2 ≠ 0)).finite_adjoinRoot
  etale := by
    letI : Fact (Irreducible (Qpoly K d)) := ⟨Qpoly_irred K d hd⟩
    letI : Field (AdjoinRoot (Qpoly K d)) := by infer_instance
    constructor
    · exact Algebra.FormallyEtale.of_isSeparable K (AdjoinRoot (Qpoly K d))
    · exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  finrank_eq_two := by
    change Module.finrank K (AdjoinRoot (Qpoly K d)) = 2
    rw [(AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C d (by norm_num : 2 ≠ 0))).finrank]
    rw [AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C]

end Scratch
