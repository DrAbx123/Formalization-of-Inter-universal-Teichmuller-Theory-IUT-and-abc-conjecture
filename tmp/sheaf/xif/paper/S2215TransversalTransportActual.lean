import tmp.sheaf.xif.paper.S2211TransferConjProofActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2215TransversalTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2211TransferConjProofActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Transport of a left transversal along a multiplicative equivalence. -/
noncomputable def S2215TransversalTransport {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) (S : H.LeftTransversal) :
    (H.map e.toMonoidHom).LeftTransversal :=
  ⟨e '' (S : Set G), by
    change Function.Bijective (fun x : (e '' (S : Set G)) × (H.map e.toMonoidHom) =>
      (x.1 : G') * (x.2 : G'))
    let φ : S × H ≃ (e '' (S : Set G)) × (H.map e.toMonoidHom) :=
      (Equiv.Set.image e.toEquiv (S : Set G) e.injective).prodCongr
        (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective)
    have hcomp :
        (fun x : (e '' (S : Set G)) × (H.map e.toMonoidHom) =>
            (x.1 : G') * (x.2 : G')) ∘ φ =
          e.toEquiv ∘ (fun y : S × H => (y.1 : G) * (y.2 : G)) := by
      funext y
      change e (y.1 : G) * e (y.2 : G) = e ((y.1 : G) * (y.2 : G))
      rw [map_mul]
    have hbij : Function.Bijective
        ((fun x : (e '' (S : Set G)) × (H.map e.toMonoidHom) =>
            (x.1 : G') * (x.2 : G')) ∘ φ) := by
      rw [hcomp]
      exact e.toEquiv.bijective.comp S.2
    exact ((Equiv.bijective_comp φ) _).mp hbij⟩

#check S2215TransversalTransport
#print axioms S2215TransversalTransport

end LeanFormal.IUT.XiFPaper.S2215TransversalTransportActual

end