import tmp.sheaf.xif.paper.S2535LocalizedIntegralClosureActual
import tmp.sheaf.xif.paper.S2533LocalizedDedekindActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial NumberField
attribute [local instance] Ideal.Quotient.field
namespace LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
variable {R S K L : Type*}
  [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [Algebra S L] [Algebra R S]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsFractionRing R K]
  [FaithfulSMul R L]
  [IsIntegralClosure S R L]
variable (f : R[X]) (p : Ideal R) [hp : p.IsMaximal]
  (P : Ideal S) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
  (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
  (hsplit : (f.map (algebraMap R L)).Splits)
/-- Reduction of f modulo p. -/
def fbar : (R ⧸ p)[X] := f.map (Ideal.Quotient.mk p)
lemma mk_aeval_eq_of (g : R[X]) (α : S) :
    Ideal.Quotient.mk P (aeval α g) =
      (g.map (Ideal.Quotient.mk p)).eval₂
        (algebraMap (R ⧸ p) (S ⧸ P)) (Ideal.Quotient.mk P α) := by
  rw [aeval_def, eval₂_map]
  rw [show (algebraMap (R ⧸ p) (S ⧸ P)).comp (Ideal.Quotient.mk p) =
      (Ideal.Quotient.mk P).comp (algebraMap R S) from by
    ext x
    exact Ideal.Quotient.algebraMap_mk_of_liesOver P p x]
  rw [← eval₂_map, eval₂_hom, eval_map]
lemma mk_aeval_derivative_eq (g : R[X]) (α : S) :
    Ideal.Quotient.mk P (aeval α (derivative g)) =
      (derivative (g.map (Ideal.Quotient.mk p))).eval₂
        (algebraMap (R ⧸ p) (S ⧸ P)) (Ideal.Quotient.mk P α) := by
  rw [derivative_map]
  exact mk_aeval_eq_of (p := p) (P := P) (g := derivative g) α
include hmonic in
lemma mk_mem_rootSet (α : S) (hα : α ∈ f.rootSet S) :
    Ideal.Quotient.mk P α ∈ (fbar f p).rootSet (S ⧸ P) := by
  rw [mem_rootSet']
  constructor
  · exact Polynomial.map_monic_ne_zero (Polynomial.Monic.map (Ideal.Quotient.mk p) hmonic)
  · rw [fbar, aeval_def, ← mk_aeval_eq_of (p := p) (P := P) (g := f) α]
    rw [mem_rootSet'] at hα
    rw [hα.2, map_zero]
include P hmonic hsep in
lemma aeval_derivative_ne_zero (α : S) (hα : α ∈ f.rootSet S) :
    aeval α (derivative f) ≠ 0 := by
  intro hzero
  have hroot : (fbar f p).eval₂ (algebraMap (R ⧸ p) (S ⧸ P))
      (Ideal.Quotient.mk P α) = 0 := by
    rw [fbar, ← mk_aeval_eq_of (p := p) (P := P) f α]
    rw [mem_rootSet'] at hα
    rw [hα.2, map_zero]
  have hne := hsep.eval₂_derivative_ne_zero
    (algebraMap (R ⧸ p) (S ⧸ P)) hroot
  apply hne
  rw [← mk_aeval_derivative_eq (p := p) (P := P) f α, hzero, map_zero]
/-- The reduction map from roots of f over S to roots of fbar over S/P. -/
noncomputable def redRoot : f.rootSet S → (fbar f p).rootSet (S ⧸ P) :=
  fun α => ⟨Ideal.Quotient.mk P α.1,
    mk_mem_rootSet (f := f) (p := p) (P := P) (hmonic := hmonic) α.1 α.2⟩

include hmonic hsplit in
lemma splits_over_S : (f.map (algebraMap R S)).Splits :=
  LeanFormal.IUT.XiFPaper.S2533LocalizedDedekindActual.splits_over_integralClosure
    (R := R) (S := S) (L := L) f hmonic hsplit

include P hmonic hsep hsplit in
lemma roots_nodup :
    (f.map (algebraMap R S)).roots.Nodup := by
  classical
  set fS := f.map (algebraMap R S) with hfS
  have hfS_monic : fS.Monic := Polynomial.Monic.map _ hmonic
  have hfS_ne : fS ≠ 0 := hfS_monic.ne_zero
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  rw [Polynomial.count_roots]
  by_contra h
  push Not at h
  have hlt : 1 < fS.rootMultiplicity a := h
  have hrootd := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hfS_ne).mp hlt
  have hmem : a ∈ f.rootSet S := by
    rw [mem_rootSet']
    constructor
    · exact Polynomial.map_monic_ne_zero hmonic
    · simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def, hfS] using hrootd.1
  have hder := aeval_derivative_ne_zero (f := f) (p := p) (P := P) (hmonic := hmonic) (hsep := hsep) a hmem
  apply hder
  simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def, hfS,
    Polynomial.derivative_map] using hrootd.2

include P hmonic hsep hsplit in
lemma card_rootSet_eq :
    Fintype.card (f.rootSet S) = f.natDegree := by
  classical
  have hsplitS : (f.map (algebraMap R S)).Splits :=
    splits_over_S (f := f) (hmonic := hmonic) (hsplit := hsplit)
  have hnodup := roots_nodup (f := f) (p := p) (P := P) (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)
  simp_rw [Polynomial.rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup hnodup, ← hsplitS.natDegree_eq_card_roots]
  exact Polynomial.Monic.natDegree_map hmonic (algebraMap R S)

include P hmonic in
lemma card_rootSet_fbar_le :
    Fintype.card ((fbar f p).rootSet (S ⧸ P)) ≤ f.natDegree := by
  classical
  have h1 : Fintype.card ((fbar f p).rootSet (S ⧸ P)) =
      (((fbar f p).aroots (S ⧸ P)).toFinset).card := Fintype.card_coe _
  rw [h1]
  calc (((fbar f p).aroots (S ⧸ P)).toFinset).card
      ≤ ((fbar f p).aroots (S ⧸ P)).card := Multiset.toFinset_card_le _
    _ = ((fbar f p).map (algebraMap (R ⧸ p) (S ⧸ P))).roots.card := rfl
    _ ≤ (fbar f p).natDegree := Polynomial.card_roots_map_le_natDegree _
    _ = f.natDegree := Polynomial.Monic.natDegree_map hmonic (Ideal.Quotient.mk p)

include P hmonic hsep hsplit in
lemma redRoot_injective : Function.Injective (redRoot f p P hmonic) := by
  classical
  rintro ⟨α, hα⟩ ⟨β, hβ⟩ h
  have hmod : Ideal.Quotient.mk P α = Ideal.Quotient.mk P β := congrArg Subtype.val h
  by_contra hne
  have hne' : α ≠ β := fun h' => hne (Subtype.ext h')
  have hsplitS : (f.map (algebraMap R S)).Splits :=
    splits_over_S (f := f) (hmonic := hmonic) (hsplit := hsplit)
  have hfS_monic : (f.map (algebraMap R S)).Monic := Polynomial.Monic.map _ hmonic
  have hfS_ne : f.map (algebraMap R S) ≠ 0 := hfS_monic.ne_zero
  have hαroot : α ∈ (f.map (algebraMap R S)).roots := by
    rw [mem_roots hfS_ne]
    rw [mem_rootSet'] at hα
    simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hα.2
  have hβroot : β ∈ (f.map (algebraMap R S)).roots := by
    rw [mem_roots hfS_ne]
    rw [mem_rootSet'] at hβ
    simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hβ.2
  have hβerase : β ∈ ((f.map (algebraMap R S)).roots.erase α) :=
    (Multiset.mem_erase_of_ne (Ne.symm hne')).mpr hβroot
  have hmemP : α - β ∈ P := Ideal.Quotient.eq.mp hmod
  have hprodmem : ((((f.map (algebraMap R S)).roots.erase α).map
      (fun γ => α - γ))).prod ∈ P :=
    Ideal.mem_of_dvd P (Multiset.dvd_prod (Multiset.mem_map.mpr ⟨β, hβerase, rfl⟩)) hmemP
  have hderiv := hsplitS.eval_root_derivative hfS_monic hαroot
  have hderivmem : aeval α (derivative f) ∈ P := by
    rw [aeval_def, ← Polynomial.eval_map, ← Polynomial.derivative_map]
    rw [hderiv]
    exact hprodmem
  have hrootbar : (fbar f p).eval₂
      (algebraMap (R ⧸ p) (S ⧸ P)) (Ideal.Quotient.mk P α) = 0 := by
    simp only [fbar]
    rw [← mk_aeval_eq_of (p := p) (P := P) f α]
    rw [mem_rootSet'] at hα
    rw [hα.2, map_zero]
  have hneDeriv := hsep.eval₂_derivative_ne_zero
    (algebraMap (R ⧸ p) (S ⧸ P)) hrootbar
  apply hneDeriv
  rw [← mk_aeval_derivative_eq (p := p) (P := P) f α]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hderivmem

include P hmonic hsep hsplit in
lemma redRoot_bijective : Function.Bijective (redRoot f p P hmonic) := by
  classical
  have hdom := card_rootSet_eq (f := f) (p := p) (P := P) (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)
  have hle := card_rootSet_fbar_le (f := f) (p := p) (P := P) (hmonic := hmonic)
  have hinj := redRoot_injective (f := f) (p := p) (P := P) (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)
  have hcard_le : Fintype.card (f.rootSet S) ≤
      Fintype.card ((fbar f p).rootSet (S ⧸ P)) :=
    Fintype.card_le_of_injective _ hinj
  have hcard : Fintype.card (f.rootSet S) =
      Fintype.card ((fbar f p).rootSet (S ⧸ P)) := by
    rw [hdom]
    exact le_antisymm (by rw [hdom] at hcard_le; exact hcard_le) hle
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩

#check redRoot_bijective
#print axioms aeval_derivative_ne_zero
end LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
end