import tmp.sheaf.xif.paper.S2587LocalizedResidueDataActual
import tmp.sheaf.xif.paper.S2587FbarIdentifyActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2588FbarIrreducibleActual

open LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2587FbarIdentifyActual
open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual

abbrev S : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

noncomputable def S2588a : S :=
  ((((S2574_lead_unit.unit : Sˣ)⁻¹ : Sˣ) : S))

noncomputable def polyMulEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    A[X] ≃* B[X] where
  toFun p := p.map (e : A →+* B)
  invFun p := p.map (e.symm : B →+* A)
  left_inv p := by
    change (p.map (e : A →+* B)).map (e.symm : B →+* A) = p
    rw [Polynomial.map_map]
    simp
  right_inv p := by
    change (p.map (e.symm : B →+* A)).map (e : A →+* B) = p
    rw [Polynomial.map_map]
    simp
  map_mul' p q := by simp only [Polynomial.map_mul]

lemma S2588_PB_irreducible (W : S2584PrimeDegreeOneWitness) :
    Irreducible (S2574P.map (Ideal.Quotient.mk W.P)) := by
  have hmap : (polyMulEquiv W.residueEquivS) (S2574P.map (Ideal.Quotient.mk W.P)) = F613 := by
    change (S2574P.map (Ideal.Quotient.mk W.P)).map W.residueEquivS.toRingHom = F613
    exact S2587_fbar_eq W
  have hF : Irreducible ((polyMulEquiv W.residueEquivS) (S2574P.map (Ideal.Quotient.mk W.P))) := by
    rw [hmap]
    exact LeanFormal.IUT.XiFPaper.S2572F613IrreducibleActual.F613_irreducible
  exact (MulEquiv.irreducible_iff
    (f := polyMulEquiv W.residueEquivS)
    (x := S2574P.map (Ideal.Quotient.mk W.P))).mp hF

lemma S2588_fbar_eq (W : S2584PrimeDegreeOneWitness) :
    fbar W = Polynomial.C (Ideal.Quotient.mk W.P S2588a) * S2574P.map (Ideal.Quotient.mk W.P) := by
  unfold fbar S2574f
  rw [Polynomial.map_mul, Polynomial.map_C]
  simp [S2588a]

lemma S2588_mk_a_unit (W : S2584PrimeDegreeOneWitness) :
    IsUnit (Ideal.Quotient.mk W.P S2588a) := by
  exact IsUnit.map (Ideal.Quotient.mk W.P) (by
    rw [S2588a]
    exact ((S2574_lead_unit.unit : Sˣ)⁻¹).isUnit)

theorem S2587FbarIrreducibleRequired_holds (W : S2584PrimeDegreeOneWitness) :
    S2587FbarIrreducibleRequired W := by
  rw [S2587FbarIrreducibleRequired]
  rw [S2588_fbar_eq]
  have hunit : IsUnit (Polynomial.C (Ideal.Quotient.mk W.P S2588a)) := by
    exact isUnit_C.mpr (S2588_mk_a_unit W)
  have hassoc : Associated (Polynomial.C (Ideal.Quotient.mk W.P S2588a) *
      S2574P.map (Ideal.Quotient.mk W.P)) (S2574P.map (Ideal.Quotient.mk W.P)) :=
    associated_unit_mul_left (S2574P.map (Ideal.Quotient.mk W.P))
      (Polynomial.C (Ideal.Quotient.mk W.P S2588a)) hunit
  exact hassoc.symm.irreducible (S2588_PB_irreducible W)

#print axioms S2587FbarIrreducibleRequired_holds

end LeanFormal.IUT.XiFPaper.S2588FbarIrreducibleActual
end
