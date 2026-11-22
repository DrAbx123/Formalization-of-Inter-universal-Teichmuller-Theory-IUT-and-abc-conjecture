import tmp.sheaf.xif.paper.S2575LocalizedR10Actual
import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2572F613IrreducibleActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2576LocalizedFbar10Actual

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2574LocalizedModelActual
open LeanFormal.IUT.XiFPaper.S2575LocalizedR10Actual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2572F613IrreducibleActual

abbrev O : Type := NumberField.RingOfIntegers S1720Field

noncomputable def W : S2584PrimeDegreeOneWitness :=
  Classical.choice S2584_witness_nonempty

noncomputable def g : O →+* ZMod 613 :=
  W.residueEquiv.toRingHom.comp (Ideal.Quotient.mk W.p)

lemma x10_not_mem_p : (x10 : O) ∉ W.p := by
  intro hx
  have hLc_under : S2574LocalizedModelActual.Lc ∈ W.p.under ℤ := by
    rw [Ideal.mem_under]
    simpa [x10] using hx
  have hspan : S2574LocalizedModelActual.Lc ∈ Ideal.span {(613 : ℤ)} := by
    rw [W.p_liesOver.over]
    exact hLc_under
  have hdvd := Ideal.mem_span_singleton.mp hspan
  norm_num [S2574LocalizedModelActual.Lc] at hdvd

lemma g_x10_ne_zero : g (x10 : O) ≠ 0 := by
  intro h0
  have hmk : Ideal.Quotient.mk W.p (x10 : O) = 0 := by
    apply W.residueEquiv.injective
    rw [map_zero]
    simpa [g] using h0
  exact x10_not_mem_p (Ideal.Quotient.eq_zero_iff_mem.mp hmk)

lemma hgUnit : ∀ y : Submonoid.powers (x10 : O), IsUnit (g y) := by
  intro y
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y.1 (x10 : O)).mp y.2
  rw [← hn, map_pow]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero n g_x10_ne_zero)

noncomputable def φ : R10 →+* ZMod 613 :=
  IsLocalization.lift (M := Submonoid.powers (x10 : O)) (S := R10)
    (P := ZMod 613) (g := g) hgUnit

lemma φ_comp_algebraMap : φ.comp (algebraMap O R10) = g :=
  IsLocalization.lift_comp (M := Submonoid.powers (x10 : O)) (S := R10)
    (P := ZMod 613) (g := g) hgUnit

#check φ_comp_algebraMap
lemma φ_comp_int : φ.comp (algebraMap ℤ R10) = Int.castRingHom (ZMod 613) := by
  rw [IsScalarTower.algebraMap_eq ℤ O R10, ← RingHom.comp_assoc, φ_comp_algebraMap]
  ext z
  simp [g]

lemma φ_surjective : Function.Surjective φ := by
  intro z
  obtain ⟨x, rfl⟩ := W.residueEquiv.surjective z
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨algebraMap O R10 c, ?_⟩
  rw [show φ (algebraMap O R10 c) = g c by
    rw [← RingHom.comp_apply, φ_comp_algebraMap]]
  rfl

def p10 : Ideal R10 := RingHom.ker φ

lemma p10_max : p10.IsMaximal := RingHom.ker_isMaximal_of_surjective φ φ_surjective

noncomputable def e : R10 ⧸ p10 ≃+* ZMod 613 :=
  RingHom.quotientKerEquivOfSurjective φ_surjective

lemma φ_inv_unit : IsUnit (φ (IsLocalization.Away.invSelf (x10 : O))) := by
  have hmul : g (x10 : O) * φ (IsLocalization.Away.invSelf (x10 : O)) = 1 := by
    have h := congrArg φ (IsLocalization.Away.mul_invSelf (S := R10) (x := (x10 : O)))
    rw [map_mul, map_one] at h
    rwa [show φ (algebraMap O R10 (x10 : O)) = g (x10 : O) by
      rw [← RingHom.comp_apply, φ_comp_algebraMap]] at h
  rw [eq_inv_of_mul_eq_one_right hmul]
  exact (hgUnit ⟨x10, Submonoid.mem_powers _⟩).inv

lemma f10_map_φ :
    f10.map φ = Polynomial.C (φ (IsLocalization.Away.invSelf (x10 : O))) *
      S2132Psi5Z.map (Int.castRingHom (ZMod 613)) := by
  change ((Polynomial.C (IsLocalization.Away.invSelf (x10 : O)) *
    S2132Psi5Z.map (algebraMap ℤ R10)).map φ) = _
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, φ_comp_int]

lemma f10_map_φ_irreducible : Irreducible (f10.map φ) := by
  rw [f10_map_φ]
  apply (irreducible_isUnit_mul (isUnit_C.mpr φ_inv_unit)).mpr
  rw [← F613_eq_map]
  exact F613_irreducible

abbrev fbar10 : (R10 ⧸ p10)[X] := f10.map (Ideal.Quotient.mk p10)

lemma quotient_comp : e.toRingHom.comp (Ideal.Quotient.mk p10) = φ := by
  ext x
  change (RingHom.quotientKerEquivOfSurjective φ_surjective)
    (Ideal.Quotient.mk p10 x) = φ x
  exact RingHom.quotientKerEquivOfSurjective_apply_mk (f := φ) φ_surjective x

lemma fbar10_map_e : f10.map φ = fbar10.map e.toRingHom := by
  rw [show φ = e.toRingHom.comp (Ideal.Quotient.mk p10) from quotient_comp.symm]
  rw [Polynomial.map_map]

theorem fbar10_irreducible : Irreducible fbar10 := by
  have hI' : Irreducible (fbar10.map e.toRingHom) := by
    rw [← fbar10_map_e]
    exact f10_map_φ_irreducible
  have heI : Irreducible ((Polynomial.mapEquiv e) fbar10) := by
    simpa [Polynomial.mapEquiv] using hI'
  exact (MulEquiv.irreducible_iff (f := Polynomial.mapEquiv e)).mp heI

theorem fbar10_natDegree : fbar10.natDegree = 12 := by
  have hdeg : (f10.map φ).natDegree = 12 := by
    rw [f10_map_φ]
    rw [Polynomial.natDegree_C_mul (IsUnit.ne_zero φ_inv_unit)]
    rw [← F613_eq_map, F613_natDegree]
  have h := congrArg Polynomial.natDegree fbar10_map_e
  rw [Polynomial.natDegree_map_eq_of_injective (f := e.toRingHom) e.injective] at h
  exact h.symm.trans hdeg

#check fbar10_irreducible
#check fbar10_natDegree
#print axioms fbar10_irreducible
#print axioms fbar10_natDegree

end LeanFormal.IUT.XiFPaper.S2576LocalizedFbar10Actual
end