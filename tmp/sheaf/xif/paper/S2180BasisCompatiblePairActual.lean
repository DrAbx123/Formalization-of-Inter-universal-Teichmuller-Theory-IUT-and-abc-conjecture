import tmp.sheaf.xif.paper.S2172AffineBasisLiftActual
import tmp.sheaf.xif.paper.S2166AffinePairCorrespondenceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual

open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual

/-- The basis-compatible map from S2009 representative pairs to affine pairs:
v is sent to the pair {e v, -e v}. -/
noncomputable def S2180PairMap
    (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion)
    (x : S2009Pairs) : S2056Pair := by
  classical
  have hv : x.1 ≠ 0 := isRep_ne_zero x.1 x.2
  let P : S2056Torsion := e x.1
  have hP0 : (P : S2056W.Point) ≠ 0 := by
    intro h
    have hP : P = 0 := Subtype.ext h
    have hPe : e x.1 = 0 := hP
    have hx0 : x.1 = 0 := e.injective (by rw [hPe]; exact (map_zero e).symm)
    exact hv hx0
  let Pnz : S2056NonzeroTorsion := ⟨P, hP0⟩
  refine ⟨{Pnz, -Pnz}, ?_, ?_⟩
  · exact Finset.card_pair (S2056_ne_neg Pnz)
  · intro Q hQ
    rw [Finset.mem_insert, Finset.mem_singleton] at hQ ⊢
    rcases hQ with rfl | rfl
    · exact Or.inr rfl
    · refine Or.inl ?_
      apply Subtype.ext
      apply Subtype.ext
      exact neg_neg _

/-- The inverse map: a pair S is sent to the normalised coordinate of any of
its two points under e. -/
noncomputable def S2180PairInv
    (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion)
    (S : S2056Pair) : S2009Pairs := by
  classical
  have hpos : 0 < S.1.card := by rw [S.2.1]; norm_num
  let P : S2056NonzeroTorsion := Classical.choose (Finset.card_pos.mp hpos)
  have hPS : P ∈ S.1 := Classical.choose_spec (Finset.card_pos.mp hpos)
  let v : Fin 2 → ZMod S1982Five.value := e.symm (P : S2056Torsion)
  have hv : v ≠ 0 := by
    intro hv0
    have hPzero : (P : S2056Torsion) = 0 := by
      rw [← e.apply_symm_apply (P : S2056Torsion)]
      change e v = 0
      rw [hv0, map_zero]
    exact P.2 (congrArg Subtype.val hPzero)
  exact ⟨normalize v, normalize_isRep v hv⟩

/-- Exact basis-compatible pair data: the pair equivalence is the map above,
with a proof that it is compatible with `S2172AffineBasis`. -/
structure S2180BasisCompatiblePairEquiv
    (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion) where
  pairEquiv : S2009Pairs ≃ S2056Pair
  pairEquiv_apply : ∀ x, pairEquiv x = S2180PairMap e x

/-- Exact first missing: the basis-compatible pair equivalence for the actual
affine basis. -/
def S2180BasisCompatiblePairEquivRequired : Prop :=
  Nonempty (S2180BasisCompatiblePairEquiv S2172AffineBasis)

end LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual

end
