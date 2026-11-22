import Iut.Tripod.SL2Generation
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7TransvectionLargeImageActual
open LeanFormal.IUT
open Matrix

variable {F : Type*} [Field F] {l : PrimeGeFive}
variable (X : PuncturedEllipticCurve F)
variable (b : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l)

local notation "ρ" => X.galoisLTorsionMatrixRepresentation l b

/-- Arithmetic-height/transvection step: a transvection in the mod-`l` image
plus the no-invariant-line condition implies the full `SL₂` image is contained
in `(X.galoisLTorsionMatrixRepresentation l b).range`.  This is the group-theoretic core of [GenEll] Lemma 3.1(iii),
using `Iut.SL2.toGL_mem_of_transvection` and not the S2835 interface. -/
theorem p7_sl2_le_range_of_transvection
    (hT : ∃ T : GL (Fin 2) (ZMod l.value), T ∈ (X.galoisLTorsionMatrixRepresentation l b).range ∧ T ≠ 1 ∧
      ((T : Matrix (Fin 2) (Fin 2) (ZMod l.value)) - 1) ^ 2 = 0)
    (hline : ∀ v : Fin 2 → ZMod l.value, v ≠ 0 →
      ∃ g ∈ (X.galoisLTorsionMatrixRepresentation l b).range, ∀ c : ZMod l.value,
        (g : Matrix (Fin 2) (Fin 2) (ZMod l.value)) *ᵥ v ≠ c • v)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) :
    A.toGL ∈ (X.galoisLTorsionMatrixRepresentation l b).range := by
  haveI : Fact l.value.Prime := ⟨l.prime⟩
  rcases hT with ⟨T, hTmem, hT1, hT2⟩
  exact Iut.SL2.toGL_mem_of_transvection (X.galoisLTorsionMatrixRepresentation l b).range hTmem hT1 hT2 hline A

#print axioms p7_sl2_le_range_of_transvection
end LeanFormal.IUT.XiFPaper.Mzk1P7TransvectionLargeImageActual