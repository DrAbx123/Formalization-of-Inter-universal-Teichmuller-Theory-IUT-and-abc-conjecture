import tmp.sheaf.xif.paper.S2539AbstractRedRootActual
import Mathlib.FieldTheory.Finite.Basic
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial NumberField
attribute [local instance] Ideal.Quotient.field
namespace LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
variable {R S K L : Type*}
  [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [Algebra S L] [Algebra R S]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsFractionRing R K]
  [FaithfulSMul R L] [IsIntegralClosure S R L]
variable (f : R[X]) (p : Ideal R) [hp : p.IsMaximal]
  (P : Ideal S) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
  (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
  (hsplit : (f.map (algebraMap R L)).Splits)
  [Fintype (R ⧸ p)] [Fintype (S ⧸ P)]
/-- Arithmetic q-Frobenius on the residue field at P. -/
noncomputable def frobBar (y : S ⧸ P) : S ⧸ P :=
  y ^ Nat.card (R ⧸ p)
lemma frobBar_mem_rootSet {y : S ⧸ P}
    (hy : y ∈ (fbar f p).rootSet (S ⧸ P)) :
    frobBar (p := p) (P := P) y ∈ (fbar f p).rootSet (S ⧸ P) := by
  rw [mem_rootSet'] at hy ⊢
  refine ⟨hy.1, ?_⟩
  have h := Polynomial.aeval_algHom_apply
    (FiniteField.frobeniusAlgHom (R ⧸ p) (S ⧸ P)) y (fbar f p)
  rw [hy.2, map_zero] at h
  have hfrob : FiniteField.frobeniusAlgHom (R ⧸ p) (S ⧸ P) y =
      y ^ Nat.card (R ⧸ p) := by
    rw [FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card]
  rw [frobBar, ← hfrob]
  exact h
lemma frobBar_injective : Function.Injective (frobBar (p := p) (P := P)) := by
  have h := RingHom.injective
    (FiniteField.frobeniusAlgHom (R ⧸ p) (S ⧸ P)).toRingHom
  intro y z hyz
  apply h
  simpa [frobBar, FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card] using hyz
/-- q-Frobenius permutation on roots of fbar. -/
noncomputable def permBar : Equiv.Perm ((fbar f p).rootSet (S ⧸ P)) :=
  Equiv.ofBijective
    (fun y => ⟨frobBar (p := p) (P := P) y.1, frobBar_mem_rootSet (f := f) (p := p) (P := P) y.2⟩)
    (Finite.injective_iff_bijective.mp (fun y z h => Subtype.ext
      (frobBar_injective (p := p) (P := P) (congrArg Subtype.val h))))
#check permBar
#print axioms frobBar_mem_rootSet
end LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
end
