import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual
import tmp.sheaf.xif.paper.S2574LocalizedP12Actual
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2572F613IrreducibleActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2587FbarIdentifyActual

open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual
open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual

abbrev S : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

variable (W : S2584PrimeDegreeOneWitness)

/-- The unnormalized integer model P reduced modulo the prime P and identified with ZMod 613. -/
noncomputable def S2587fbar : (ZMod 613)[X] :=
  (S2574P.map (Ideal.Quotient.mk W.P)).map W.residueEquivS.toRingHom

lemma S2587_comp_eq :
    W.residueEquivS.toRingHom.comp ((Ideal.Quotient.mk W.P).comp (algebraMap ℤ S)) =
      Int.castRingHom (ZMod 613) :=
  RingHom.ext_int _ _

lemma S2587_fbar_eq : S2587fbar W = F613 := by
  unfold S2587fbar S2574P
  simp only [Polynomial.map_map]
  rw [show W.residueEquivS.toRingHom.comp
      ((Ideal.Quotient.mk W.P).comp (algebraMap ℤ S)) =
        Int.castRingHom (ZMod 613) from S2587_comp_eq W]
  rw [← F613_eq_map]

theorem S2587_fbar_degree : (S2587fbar W).natDegree = 12 := by
  rw [S2587_fbar_eq]
  exact F613_natDegree

theorem S2587_fbar_irreducible : Irreducible (S2587fbar W) := by
  rw [S2587_fbar_eq]
  exact LeanFormal.IUT.XiFPaper.S2572F613IrreducibleActual.F613_irreducible

#print axioms S2587_fbar_irreducible

end LeanFormal.IUT.XiFPaper.S2587FbarIdentifyActual
end
