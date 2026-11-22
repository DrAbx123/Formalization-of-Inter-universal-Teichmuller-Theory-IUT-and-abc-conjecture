import tmp.sheaf.xif.paper.S2069GroupAlgorithmGap
import tmp.sheaf.xif.paper.S2060CompletionUnitsActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2069GroupAlgorithmGap
namespace LeanFormal.IUT.XiFPaper.S2070AbsTopIIIAlgorithmGap
variable {G : Type*} {V : Type*}
/-- The missing [AbsTopIII], Proposition 5.8(i), functorial group-theoretic
algorithm `G -> O^◃(G)` of IUT II, Example 1.8(ii), before taking units and
the torsion quotient.  No inhabitant is asserted. -/
structure S2070OtriangleAlgorithm where
  Otri : ProfiniteGrp → Type
  [commMonoidOtri : ∀ G : ProfiniteGrp, CommMonoid (Otri G)]
  map : ∀ {G H : ProfiniteGrp}, G ≃* H → Otri G ≃* Otri H
noncomputable def s2070TimesMuCongr {U W : Type*} [CommGroup U] [CommGroup W]
    (e : U ≃* W) : TimesMuQuotient U ≃* TimesMuQuotient W :=
  QuotientGroup.congr (CommGroup.torsion U) (CommGroup.torsion W) e e.map_torsion
noncomputable def S2070Units (A : S2070OtriangleAlgorithm)
    (G : ProfiniteGrp) : Type := by
  letI : CommMonoid (A.Otri G) := A.commMonoidOtri G
  exact TimesMuQuotient (Units (A.Otri G))
noncomputable instance S2070Units_commMonoid (A : S2070OtriangleAlgorithm)
    (G : ProfiniteGrp) : CommMonoid (S2070Units A G) := by
  unfold S2070Units
  letI : CommMonoid (A.Otri G) := A.commMonoidOtri G
  infer_instance
/-- From the missing O^◃ algorithm, the O^×μ algorithm of Example 1.8(iv)
follows by units plus the torsion quotient. -/
noncomputable def S2070UnitsMuAlgorithm
    (A : S2070OtriangleAlgorithm) : S2069GroupAlgorithmReconstruction where
  units := S2070Units A
  commMonoidUnits := fun G => S2070Units_commMonoid A G
  map := by
    intro G H e
    letI : CommMonoid (A.Otri G) := A.commMonoidOtri G
    letI : CommMonoid (A.Otri H) := A.commMonoidOtri H
    exact s2070TimesMuCongr (Units.mapEquiv (A.map e))
/-- Exact first missing at the paper level: an inhabitant is the
[AbsTopIII], Proposition 5.8(i), algorithm G -> O^◃(G), not available in the
tree.  The O^×μ algorithm is derived from it above. -/
abbrev S2070OtriangleAlgorithmRequired : Type 1 := S2070OtriangleAlgorithm
#check S2070OtriangleAlgorithm
#check S2070UnitsMuAlgorithm
#check S2070OtriangleAlgorithmRequired
end LeanFormal.IUT.XiFPaper.S2070AbsTopIIIAlgorithmGap
end
