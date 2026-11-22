import Mathlib
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma23SeparationActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- The separation value 1/(x - lambda) of paper [Mzk1] Lemma 2.3 (rational version). -/
def sepValue (lam x : ℚ) : ℚ := (x - lam)⁻¹

/-- **Rational separation, metric core** (paper [Mzk1] Lemma 2.3, lines 163-165, rational
version): for finite S subset Q and beta in Q minus S there is a rational lambda outside S
and different from beta such that beta is strictly closer to lambda than every alpha in S.
Proof: the minimum distance delta of beta from S is positive (S finite, beta not in S);
take lambda = beta + delta/4. -/
theorem s3135_separation_rat (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) :
    ∃ lam : ℚ, lam ∉ S ∧ lam ≠ β ∧ ∀ α ∈ S, |β - lam| < |α - lam| := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hne
  · subst hS
    exact ⟨β + 1, by simp, by simp, by simp⟩
  · let δ : ℚ := (S.image (fun α => |β - α|)).min' (hne.image _)
    have hδmem : δ ∈ S.image (fun α => |β - α|) := Finset.min'_mem _ _
    obtain ⟨α0, hα0, hδeq⟩ := Finset.mem_image.mp hδmem
    have hβα0 : β ≠ α0 := fun h => hβ (h ▸ hα0)
    have hδpos : 0 < δ := by
      rw [← hδeq]
      exact abs_pos.mpr (sub_ne_zero.mpr hβα0)
    have hδle : ∀ α ∈ S, δ ≤ |β - α| := by
      intro α hα
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨α, hα, rfl⟩)
    refine ⟨β + δ / 4, ?_, ?_, ?_⟩
    · intro hmem
      have hle : δ ≤ |β - (β + δ / 4)| := hδle _ hmem
      have hval : |β - (β + δ / 4)| = δ / 4 := by
        rw [show β - (β + δ / 4) = -(δ / 4) by ring, abs_neg, abs_of_pos (by positivity)]
      rw [hval] at hle
      linarith
    · intro h
      have hδzero : δ = 0 := by
        have : β = β + δ / 4 := h.symm
        linarith
      linarith
    · intro α hα
      have hαβ : δ ≤ |β - α| := hδle α hα
      have hαβ' : δ ≤ |α - β| := by rw [abs_sub_comm]; exact hαβ
      have hkey : |α - β| ≤ |α - (β + δ / 4)| + |(β + δ / 4) - β| := by
        calc |α - β| = |(α - (β + δ / 4)) + ((β + δ / 4) - β)| := by ring_nf
          _ ≤ |α - (β + δ / 4)| + |(β + δ / 4) - β| := abs_add_le _ _
      have hlam : |(β + δ / 4) - β| = δ / 4 := by
        rw [show (β + δ / 4) - β = δ / 4 by ring, abs_of_pos (by positivity)]
      have hβlam : |β - (β + δ / 4)| = δ / 4 := by
        rw [show β - (β + δ / 4) = -(δ / 4) by ring, abs_neg, abs_of_pos (by positivity)]
      rw [hlam] at hkey
      rw [hβlam]
      linarith

/-- **Rational separation with the 1/(x - lambda) value** (paper [Mzk1] Lemma 2.3,
rational version): the selected lambda gives sepValue(lambda, beta) = 0-free, finite on S,
and strictly larger in absolute value than every sepValue(lambda, alpha), alpha in S. -/
theorem s3135_separation_rat_value (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) :
    ∃ lam : ℚ, lam ∉ S ∧ sepValue lam β ≠ 0 ∧
      (∀ α ∈ S, α ≠ lam) ∧ (∀ α ∈ S, |sepValue lam α| < |sepValue lam β|) := by
  obtain ⟨lam, hlamS, hlamβ, hineq⟩ := s3135_separation_rat S β hβ
  refine ⟨lam, hlamS, ?_, ?_, ?_⟩
  · exact inv_ne_zero (sub_ne_zero.mpr (fun h => hlamβ h.symm))
  · intro α hα hEq
    exact hlamS (hEq ▸ hα)
  · intro α hα
    have hlt : |β - lam| < |α - lam| := hineq α hα
    have hbpos : 0 < |β - lam| := abs_pos.mpr (sub_ne_zero.mpr (fun h => hlamβ h.symm))
    have hapos : 0 < |α - lam| := abs_pos.mpr (sub_ne_zero.mpr (fun h => hlamS (h ▸ hα)))
    have h1 : 1 / |α - lam| < 1 / |β - lam| := one_div_lt_one_div_of_lt hbpos hlt
    have : (|α - lam|)⁻¹ < (|β - lam|)⁻¹ := by simpa [one_div] using h1
    simpa [sepValue, abs_inv, one_div] using this

/-- **Paper-scope separation statement over Qbar** (statement only, named): for a fixed
Q-algebra embedding of Qbar into C, every finite S subset P1(Qbar) and beta outside S
admit rational lambda separating beta from S in the complex absolute value of the images
(the paper [Mzk1] Lemma 2.3 separation used in lines 163-165).  This is the Layer A 2.3
application statement; not proved here (Qbar norm requires the chosen embedding). -/
def QbarSeparationPaperStatement (emb : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) : Prop :=
  ∀ (S : Finset (AlgebraicClosure ℚ)) (β : AlgebraicClosure ℚ), β ∉ S →
    ∃ lam : ℚ, (algebraMap ℚ (AlgebraicClosure ℚ) lam) ∉ S ∧
      (algebraMap ℚ (AlgebraicClosure ℚ) lam) ≠ β ∧
      (∀ α ∈ S, Complex.normSq ((emb α - (algebraMap ℚ ℂ lam))⁻¹) <
        Complex.normSq ((emb β - (algebraMap ℚ ℂ lam))⁻¹))

/-- Status: rational separation (metric core + 1/(x-lambda) value form) PROVED; paper-scope
Qbar statement filed as named Layer A statement.  No closure claim; binding HOLD. -/
def SeparationStatus : Audit.Obligation :=
  { id := "MZK1.lemma23.separation"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.3 lines 163-165; Lead A384 assignment (Qbar Layer A small steps)"
    status := Audit.VerificationStatus.interface
    note := "PROVED (rational version): s3135_separation_rat (exists rational lambda outside S, lambda != beta, beta strictly closer to lambda than every alpha in S; min-distance delta = min over S of |beta-alpha| > 0, lambda = beta + delta/4) and s3135_separation_rat_value (sepValue lambda beta != 0, alpha != lambda for alpha in S, and |sepValue lambda alpha| < |sepValue lambda beta| all alpha in S, using abs_inv + inv_lt_inv_of_lt). STATEMENT ONLY (named, Layer A 2.3 application): QbarSeparationPaperStatement (fixed Q-algebra embedding Qbar -> C; finite S in P1(Qbar), beta outside S; rational lambda separating complex absolute values). This fills the mobius23Row statement slot of the Layer A consumer; proof of the Qbar version needs the embedding/metric layer. No closure claim; binding HOLD; gate NOT PASSED; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.paper-scope" ]
    sorryItems :=
      [ "QbarSeparationPaperStatement (paper-scope 2.3 separation over Qbar/C, statement only)",
        "Moebius/P1 formulation of the rational separation value (f(x) = 1/(x - lambda) with f(beta) not in {0, inf}, f(alpha) != inf, ratio bound)" ] }

#check s3135_separation_rat
#check s3135_separation_rat_value
#check QbarSeparationPaperStatement
end LeanFormal.IUT.XiFPaper.Mzk1Lemma23SeparationActual
end