import Mathlib
import tmp.sheaf.xif.paper.Mzk1Lemma24UnionActual
import tmp.sheaf.xif.paper.Mzk1Lemma24StepProvider2Actual
import tmp.sheaf.xif.paper.Mzk1Lemma24StepProviderActual
import tmp.sheaf.xif.paper.Mzk1Lemma24ValueDegreeDropActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24StepProvider3Actual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma24UnionActual

abbrev Qbar : Type := AlgebraicClosure ℚ

local instance : DecidableEq Qbar := Classical.decEq Qbar
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24StepProvider2Actual

 /-- **(S2-i) First-alternative measure decrease for the critical-value part f0(S0)**
(paper [Mzk1] Lemma 2.4 lines 195-203): for f0 = minpoly(alpha0) of degree d0 >= 2 and
any nonempty finite set S0 of roots of f0', the set f0(S0) has maximal reduced degree
strictly smaller than m({alpha0}) = d0 - 1.  Proof: (S1b) value-degree drop gives
[Q(f0(x)):Q] <= d0 - 1 hence reducedDegree <= d0 - 2 < d0 - 1, and the generic (S2)
first-alternative lemma applies. -/
theorem s3135_f0S0_m_lt (α0 : Qbar) (S0 : Finset Qbar)
    (hd0 : 2 ≤ (minpoly ℚ α0).natDegree)
    (hS0 : ∀ x ∈ S0, Polynomial.aeval x (Polynomial.derivative (minpoly ℚ α0)) = 0)
    (hS0ne : S0.Nonempty) :
    mOfPoints (S0.image (fun x => Polynomial.aeval x (minpoly ℚ α0)))
        (hS0ne.image _)
      < mOfPoints ({α0} : Finset Qbar) (Finset.singleton_nonempty α0) := by
  have hsingle : mOfPoints ({α0} : Finset Qbar) (Finset.singleton_nonempty α0) =
      (minpoly ℚ α0).natDegree - 1 := by
    unfold mOfPoints
    simp [reducedDegreeOfPoint]
  have hd0' : 1 ≤ (minpoly ℚ α0).natDegree := by omega
  have hlt : ∀ β ∈ S0.image (fun x => Polynomial.aeval x (minpoly ℚ α0)),
      reducedDegreeOfPoint β < mOfPoints ({α0} : Finset Qbar) (Finset.singleton_nonempty α0) := by
    intro β hβ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hβ
    have hdrop : (minpoly ℚ (Polynomial.aeval x (minpoly ℚ α0))).natDegree ≤
        (minpoly ℚ α0).natDegree - 1 :=
      Mzk1Lemma24ValueDegreeDropActual.valueDegreeDrop_proved α0 x hd0' (hS0 x hx)
    rw [hsingle]
    unfold reducedDegreeOfPoint
    omega
  exact s3135_mOfPoints_lt_of_forall_reducedDegree_lt
    ({α0} : Finset Qbar) (S0.image (fun x => Polynomial.aeval x (minpoly ℚ α0)))
    (Finset.singleton_nonempty α0) (hS0ne.image _) hlt

/-- Status: (S2-i) critical-value part of the measure decrease PROVED (f0(S0) has
m < m({alpha0}) = d0-1); remaining StepProvider residue: (i-b) the f0(S) part and the
combined S' = f0(S union S0) bookkeeping; (ii) f0 morphism data wiring from ShapeStep;
(iii) equal-m d-decrease branch; (iv) final assembly.  Registry frozen 14041. -/
def Mzk1Lemma24StepProvider3Status : Audit.Obligation :=
  { id := "MZK1.lemma24.step-provider.3"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 195-206"
    status := Audit.VerificationStatus.interface
    note := "PROVED: s3135_f0S0_m_lt (critical-value part: f0(S0) has maximal reduced degree < m({alpha0}) = d0-1, using stepxi S1b valueDegreeDrop_proved + our S2 generic first-alternative lemma). EXTERNAL PROVED INPUTS: S1a (ours), S1b (stepxi Mzk1Lemma24ValueDegreeDropActual), S2 generic + S3 goal transport (ours Mzk1Lemma24StepProvider2Actual), rational base provider (hull). REMAINING: (i-b) f0(S) part and combined S'=f0(S union S0) bookkeeping; (ii) f0 morphism data wiring from ShapeStep; (iii) equal-m d-decrease branch; (iv) final assembly of Mzk1Lemma24StepProviderStatement. No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.step-provider.2" ]
    sorryItems :=
      [ "(i-b) f0(S) part + combined S' bookkeeping",
        "(ii) f0 morphism data wiring from ShapeStep",
        "(iii) equal-m d-decrease branch",
        "(iv) final StepProvider assembly" ] }

#check s3135_f0S0_m_lt
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24StepProvider3Actual
end