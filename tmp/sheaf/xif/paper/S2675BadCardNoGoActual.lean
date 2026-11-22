import tmp.sheaf.xif.paper.S1895OIdentificationsActual
import tmp.sheaf.xif.paper.S1527OOrderEqualityActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

namespace LeanFormal.IUT.XiFPaper.S2675BadCardNoGoActual

theorem S2675_S1280Bad_card (l : PrimeGeFive) :
    Fintype.card (Bad (S1280Selection l)) = 1 := by
  classical
  haveI : Subsingleton (Bad (S1280Selection l)) :=
    S1280Bad_subsingleton l
  have hne : Nonempty (Bad (S1280Selection l)) := ⟨
    Classical.choose (S1280Selection_V_mod_bad_nonempty l),
    Classical.choose_spec (S1280Selection_V_mod_bad_nonempty l)⟩
  obtain ⟨x⟩ := hne
  exact Fintype.card_eq_one_iff.mpr ⟨x, fun y => Subsingleton.elim y x⟩

theorem S2675_paperInput_bad_card (D : S1895PaperInput) :
    Nat.card (S1895PaperInput.I D).initial.badPlaces = 1 := by
  change Nat.card (Bad (S1280Selection D.l)) = 1
  letI : Fintype (Bad (S1280Selection D.l)) := S1280BadFintype D.l
  rw [Nat.card_eq_fintype_card]
  exact S2675_S1280Bad_card D.l

theorem S2675_not_five_le (D : S1895PaperInput) :
    ¬ 5 ≤ Nat.card (S1895PaperInput.I D).initial.badPlaces := by
  rw [S2675_paperInput_bad_card D]
  norm_num

#check S2675_S1280Bad_card
#check S2675_paperInput_bad_card
#check S2675_not_five_le
#print axioms S2675_paperInput_bad_card

end LeanFormal.IUT.XiFPaper.S2675BadCardNoGoActual
end
