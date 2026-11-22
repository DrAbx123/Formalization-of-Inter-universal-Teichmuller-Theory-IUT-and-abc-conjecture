import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual
import tmp.sheaf.xif.paper.S2572F613IrreducibleActual
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2003Psi5ModelActual
import Mathlib.FieldTheory.Perfect
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2007F613FbarActual

set_option maxHeartbeats 8000000

open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2572F613IrreducibleActual
open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2003Psi5ModelActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual

local instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

/-- The nonmonic integral model of `2^36 * psi_5` over `O_{F'}`. -/
noncomputable def S2007f : C[X] := S2132Psi5Z.map (Int.castRingHom C)

theorem S2007fbar_map_eq (W : S2584PrimeDegreeOneWitness) :
    (Polynomial.mapEquiv W.residueEquiv) (fbar S2007f W.p) =
      S2132Psi5Z.map (Int.castRingHom (ZMod 613)) := by
  have hcomp :
      W.residueEquiv.toRingHom.comp
        ((Ideal.Quotient.mk W.p).comp (Int.castRingHom C)) =
      Int.castRingHom (ZMod 613) := by
    ext z
    simp
  simp [Polynomial.mapEquiv, fbar, S2007f, Polynomial.map_map]
  change S2132Psi5Z.map
    (W.residueEquiv.toRingHom.comp
      ((Ideal.Quotient.mk W.p).comp (Int.castRingHom C))) =
    S2132Psi5Z.map (Int.castRingHom (ZMod 613))
  rw [hcomp]

theorem S2007fbar_irreducible (W : S2584PrimeDegreeOneWitness) :
    Irreducible (fbar S2007f W.p) := by
  have hI : Irreducible
      ((Polynomial.mapEquiv W.residueEquiv) (fbar S2007f W.p)) := by
    rw [S2007fbar_map_eq W]
    rw [← F613_eq_map]
    exact F613_irreducible
  exact (MulEquiv.irreducible_iff
    (f := Polynomial.mapEquiv W.residueEquiv)).mp hI

theorem S2007f_map_scalar :
    S2007f.map (algebraMap C S1720Field) =
      Polynomial.C ((2 : S1720Field) ^ 36) * S2057Psi5F := by
  unfold S2007f S2057Psi5F
  rw [Polynomial.map_map]
  have hcomp : (algebraMap C S1720Field).comp (Int.castRingHom C) =
      Int.castRingHom S1720Field := by
    ext z
    simp
  rw [hcomp]
  have hcompQ : (algebraMap ℚ S1720Field).comp (Int.castRingHom ℚ) =
      Int.castRingHom S1720Field := by
    ext z
    simp
  have h := congrArg (Polynomial.map (algebraMap ℚ S1720Field)) S2003Psi5Z_model
  simpa [Polynomial.map_map, Polynomial.map_mul, Polynomial.map_C, hcompQ] using h

theorem S2007fbar_natDegree (W : S2584PrimeDegreeOneWitness) :
    (fbar S2007f W.p).natDegree = 12 := by
  have hmap : (fbar S2007f W.p).map W.residueEquiv.toRingHom =
      S2132Psi5Z.map (Int.castRingHom (ZMod 613)) := by
    simpa [Polynomial.mapEquiv] using S2007fbar_map_eq W
  have h := congrArg Polynomial.natDegree hmap
  rw [Polynomial.natDegree_map_eq_of_injective W.residueEquiv.injective] at h
  rw [← F613_eq_map, F613_natDegree] at h
  exact h

#check S2007fbar_natDegree
#check S2007f_map_scalar
#check S2007fbar_irreducible
#print axioms S2007fbar_natDegree
#print axioms S2007f_map_scalar
#print axioms S2007fbar_irreducible
end LeanFormal.IUT.XiFPaper.S2007F613FbarActual
end