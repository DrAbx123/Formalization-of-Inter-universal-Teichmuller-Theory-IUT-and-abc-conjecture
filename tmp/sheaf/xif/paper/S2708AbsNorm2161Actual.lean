import tmp.sheaf.xif.paper.S2698Two2161ResidueActual
import tmp.sheaf.xif.paper.S2701GaussianPrimeIdealsActual

noncomputable section
set_option maxRecDepth 100000
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2697Two2161PlacesActual
open LeanFormal.IUT.XiFPaper.S2698Two2161ResidueActual
open LeanFormal.IUT.XiFPaper.S2701GaussianPrimeIdealsActual

namespace LeanFormal.IUT.XiFPaper.S2708AbsNorm2161Actual

local instance s2708Fact2161 : Fact (Nat.Prime 2161) := ⟨S2697Prime2161⟩

theorem S2708_absNorm_plus :
    (S2697GaussianFieldPrimePlus).absNorm = 2161 := by
  rw [Ideal.absNorm_apply]
  rw [Submodule.cardQuot_apply]
  calc Nat.card (gaussianRingOfIntegers ⧸ S2697GaussianFieldPrimePlus)
      = Nat.card (ZMod 2161) :=
        Nat.card_congr S2698FieldResidueEquivPlus.toEquiv
    _ = 2161 := Nat.card_zmod 2161

theorem S2708_absNorm_minus :
    (S2697GaussianFieldPrimeMinus).absNorm = 2161 := by
  rw [Ideal.absNorm_apply]
  rw [Submodule.cardQuot_apply]
  calc Nat.card (gaussianRingOfIntegers ⧸ S2697GaussianFieldPrimeMinus)
      = Nat.card (ZMod 2161) :=
        Nat.card_congr S2698FieldResidueEquivMinus.toEquiv
    _ = 2161 := Nat.card_zmod 2161

theorem S2708_inertiaDeg_eq_one_of_absNorm
    (P : Ideal gaussianRingOfIntegers)
    [P.LiesOver (Ideal.span {(2161 : ℤ)})]
    (habs : P.absNorm = 2161) :
    (Ideal.span {(2161 : ℤ)}).inertiaDeg' P = 1 := by
  have hpow := Ideal.absNorm_eq_pow_inertiaDeg' P (p := 2161) S2697Prime2161
  rw [habs] at hpow
  have hinj : Function.Injective (fun n : ℕ => 2161 ^ n) :=
    Nat.pow_right_injective (by norm_num)
  exact hinj (by simpa using hpow.symm)

#check S2708_absNorm_plus
#check S2708_absNorm_minus
#check S2708_inertiaDeg_eq_one_of_absNorm
#print axioms S2708_absNorm_plus
#print axioms S2708_absNorm_minus

end LeanFormal.IUT.XiFPaper.S2708AbsNorm2161Actual
end
