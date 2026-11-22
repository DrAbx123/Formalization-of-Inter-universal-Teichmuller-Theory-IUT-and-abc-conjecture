import tmp.sheaf.xif.paper.S2651RootMapActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual

noncomputable section
set_option maxHeartbeats 4000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2651RootMapActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

namespace LeanFormal.IUT.XiFPaper.S2652RootBijectionActual

variable (f : (RingOfIntegers S1720Field)[X])
  (p : Ideal (RingOfIntegers S1720Field)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers S2057FiveDivisionField)) [hP : P.IsPrime]
  [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers S1720Field)
    S2057FiveDivisionField)).Splits)
  (c : S1720Field) (hc : c ≠ 0)
  (hK : f.map (algebraMap (RingOfIntegers S1720Field) S2056K) =
    C (algebraMap S1720Field S2056K c) * (S2056W.preΨ (5 : ℤ)))

include hp hP hPover hmonic hsep hsplit hc hK in
theorem S2652_natDegree : f.natDegree = 12 := by
  have hpre : (S2056W.preΨ (5 : ℤ)).natDegree = 12 := by
    rw [WeierstrassCurve.natDegree_preΨ (W := S2056W) (n := 5)
      (by norm_num : ((5 : ℤ) : S2056K) ≠ 0)]
    norm_num
  have hc0 : Polynomial.C (algebraMap S1720Field S2056K c) ≠ 0 :=
    Polynomial.C_ne_zero.mpr (by
      intro h
      exact hc ((algebraMap S1720Field S2056K).injective (by simpa using h)))
  have hinj : Function.Injective
      (algebraMap (RingOfIntegers S1720Field) S2056K) :=
    (algebraMap S1720Field S2056K).injective.comp
      (IsFractionRing.injective (RingOfIntegers S1720Field) S1720Field)
  have h := congrArg Polynomial.natDegree hK
  rw [Polynomial.natDegree_map_eq_of_injective hinj f] at h
  rw [Polynomial.natDegree_mul hc0 S2056W_preΨ_ne_zero, hpre,
    Polynomial.natDegree_C, zero_add] at h
  exact h

include hp hP hPover hmonic hsep hsplit hc hK in
theorem S2652_card_rootSet :
    Fintype.card (f.rootSet (RingOfIntegers S2057FiveDivisionField)) = 12 := by
  rw [card_rootSet_eq f p P hmonic hsep hsplit, S2652_natDegree f p P hmonic hsep hsplit c hc hK]

include hp hP hPover hmonic hsep hsplit hc hK in
noncomputable def S2652RootEquiv :
    f.rootSet (RingOfIntegers S2057FiveDivisionField) ≃ S2056Root :=
  Equiv.ofBijective (S2651RootMap f c hc hK) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨S2651RootMap_injective f c hc hK, ?_⟩
    rw [S2652_card_rootSet f p P hmonic hsep hsplit c hc hK,
      ← Nat.card_eq_fintype_card, ← S2056Root_card])

#check S2652_natDegree
#check S2652_card_rootSet
#check S2652RootEquiv
#print axioms S2652RootEquiv

end LeanFormal.IUT.XiFPaper.S2652RootBijectionActual
end
