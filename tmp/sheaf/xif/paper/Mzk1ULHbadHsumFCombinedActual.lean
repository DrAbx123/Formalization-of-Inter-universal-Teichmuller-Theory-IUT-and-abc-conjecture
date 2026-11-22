/- hsumF 组合: hsumF_spectrum + FiberAggregate.sum_fiber_aggregate（emmy DONE 14:22:04）。
   S = 有限谱集, T = 有理素数集, fib p := S.filter (fun P => natAbs(underIntGen P)=p);
   biUnion fib = S (需要 hT: 每个 P∈S 的 under 生成元 natAbs ∈ T).
   => Sum_{P∈S} localLogF = Sum_{p∈T} Sum_{P in fib p} localLogF（再 = [K:Q] logConductorDeg）。 -/
import tmp.sheaf.xif.paper.Mzk1ULFiberAggregateActual
import tmp.sheaf.xif.paper.Mzk1ULHbadHsumFActual
import tmp.sheaf.xif.paper.Mzk1ULLocalConductorDegActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadHsumFCombinedActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULLocalConductorDegActual
open LeanFormal.IUT.XiFPaper.Mzk1ULFiberAggregateActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHbadHsumFActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual

variable (K : Type*) [Field K] [NumberField K]

/-- fiber 聚合: Sum_{P∈S} localLogF = Sum_{p∈T} Sum_{P∈S.filter(under=p)} localLogF。 -/
theorem hsumF_fiber [DecidableEq (IsDedekindDomain.HeightOneSpectrum (𝓞 K))]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (T : Finset ℕ)
    (hT : ∀ P ∈ S, (underIntGen (K := K) (P : Ideal (𝓞 K))).natAbs ∈ T) :
    (∑ P ∈ S, localLogF K P) =
      ∑ p ∈ T, ∑ P ∈ S.filter (fun (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) =>
          (underIntGen (K := K) (P : Ideal (𝓞 K))).natAbs = p),
        localLogF K P := by
  classical
  let fib : ℕ → Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := fun p =>
    S.filter (fun (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) =>
      (underIntGen (K := K) (P : Ideal (𝓞 K))).natAbs = p)
  have hfib : (T : Set ℕ).PairwiseDisjoint fib := by
    intro p _ q _ hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro P hP hQ
    simp only [fib, Finset.mem_filter] at hP hQ
    exact hpq (hP.2 ▸ hQ.2 ▸ rfl)
  have hbiU : T.biUnion fib = S := by
    ext P
    constructor
    · intro hP
      simp only [Finset.mem_biUnion] at hP
      obtain ⟨p, _, hPS⟩ := hP
      exact (Finset.mem_filter.mp hPS).1
    · intro hPS
      exact Finset.mem_biUnion.mpr ⟨_, hT P hPS, by simp [fib, hPS]⟩
  have hagg := sum_fiber_aggregate (s := T) (fib := fib)
    (f := fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => localLogF K P) hfib
  rw [hbiU] at hagg
  exact hagg.symm

/-- hsumF 的完整谱层恒等（fiber 聚合 + donor 的 [K:Q] 归一）。 -/
theorem hsumF_combined [DecidableEq (IsDedekindDomain.HeightOneSpectrum (𝓞 K))]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (T : Finset ℕ)
    (hT : ∀ P ∈ S, (underIntGen (K := K) (P : Ideal (𝓞 K))).natAbs ∈ T) :
    (∑ p ∈ T, ∑ P ∈ S.filter (fun P => (underIntGen (K := K) (P : Ideal (𝓞 K))).natAbs = p),
        localLogF K P) =
      (Module.finrank ℚ K : ℝ) * logConductorDeg K S := by
  rw [← hsumF_fiber K S T hT]
  exact hsumF_spectrum K S

#print axioms hsumF_fiber
#print axioms hsumF_combined

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadHsumFCombinedActual