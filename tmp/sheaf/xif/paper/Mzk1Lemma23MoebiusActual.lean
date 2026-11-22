import Mathlib
import tmp.sheaf.xif.paper.Mzk1MoebiusP1Actual
import tmp.sheaf.xif.paper.Mzk1MoebiusP1CActual
import tmp.sheaf.xif.paper.Mzk1Lemma23SeparationActual
import tmp.sheaf.xif.paper.Mzk1LayerAConsumerActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma23MoebiusActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1Actual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma23SeparationActual

/-- The rational Moebius map N(x) = C/(x - lam) of paper Lemma 2.3, as a P1 self-map with
rational coefficients. -/
def sepMoebius (lam C : ℚ) (hC : C ≠ 0) : MoebiusData where
  a := 0
  b := C
  c := 1
  d := -lam
  det := by
    show (0 : ℚ) * (-lam) - C * 1 ≠ 0
    rw [zero_mul, zero_sub]
    exact neg_ne_zero.mpr (by simpa using hC)

/-- N(infinity) = 0 for the separation Moebius map. -/
theorem sepMoebius_mapPoints_infty (lam C : ℚ) (hC : C ≠ 0) :
    (sepMoebius lam C hC).mapPoints P1Point.infty = P1Point.ofFinite (0 : ℚ) := by
  simp [sepMoebius, MoebiusData.mapPoints, P1Point.infty, P1Point.ofFinite]

/-- N is finite at finite points x != lam, with value C/(x - lam). -/
theorem sepMoebius_mapPoints_finite (lam C : ℚ) (hC : C ≠ 0) (x : ℚ) (hx : x ≠ lam) :
    (sepMoebius lam C hC).mapPoints (P1Point.ofFinite x) =
      P1Point.ofFinite (C / (x - lam)) := by
  have hden : (1 : ℚ) * x + -lam ≠ 0 := by
    simpa [sub_eq_add_neg] using sub_ne_zero.mpr hx
  simp only [sepMoebius, MoebiusData.mapPoints, P1Point.ofFinite]
  rw [if_neg hden]
  congr 1
  ring_nf

/-- The pole of the separation Moebius map is exactly lam (N(lam) = infinity). -/
theorem sepMoebius_mapPoints_pole (lam C : ℚ) (hC : C ≠ 0) :
    (sepMoebius lam C hC).mapPoints (P1Point.ofFinite lam) = P1Point.infty := by
  simp [sepMoebius, MoebiusData.mapPoints, P1Point.ofFinite]

/-- Paper Lemma 2.3 in P1/Moebius form (rational version, PROVED): from the proved
separation, with C := beta - lam, the rational Moebius map N(x) = C/(x - lam) has
rational coefficients, N(beta) finite and nonzero (it equals 1), N(alpha) finite for all
alpha in S, |N(alpha)| <= 1 on S, no critical values, and is nonconstant. -/
theorem s3135_mobius_separation (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) :
    ∃ (lam C : ℚ) (hC : C ≠ 0),
      (sepMoebius lam C hC).mapPoints (P1Point.ofFinite β) ≠ P1Point.ofFinite (0 : ℚ) ∧
      (sepMoebius lam C hC).mapPoints (P1Point.ofFinite β) ≠ P1Point.infty ∧
      (∀ α ∈ S, (sepMoebius lam C hC).mapPoints (P1Point.ofFinite α) ≠ P1Point.infty) ∧
      (∀ α ∈ S, |C / (α - lam)| ≤ 1) ∧
      (moebiusCriticalValues (sepMoebius lam C hC) = ∅) ∧
      (∃ p q : P1Point ℚ, (sepMoebius lam C hC).mapPoints p ≠ (sepMoebius lam C hC).mapPoints q) := by
  obtain ⟨lam, hlamS, hlamβ, hineq⟩ := s3135_separation_rat S β hβ
  have hβlam : β - lam ≠ 0 := sub_ne_zero.mpr (fun h => hlamβ h.symm)
  refine ⟨lam, β - lam, hβlam, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sepMoebius_mapPoints_finite lam (β - lam) hβlam β (fun h => hlamβ h.symm)]
    intro h
    have h1 : (β - lam) / (β - lam) = 1 := div_self hβlam
    have h2 : (1 : ℚ) = 0 := by rw [← h1]; exact Option.some.inj h
    norm_num at h2
  · rw [sepMoebius_mapPoints_finite lam (β - lam) hβlam β (fun h => hlamβ h.symm)]
    exact P1Point.ofFinite_ne_infty _
  · intro α hα
    rw [sepMoebius_mapPoints_finite lam (β - lam) hβlam α (fun h => hlamS (h ▸ hα))]
    exact P1Point.ofFinite_ne_infty _
  · intro α hα
    have hlt : |β - lam| < |α - lam| := hineq α hα
    have hαne : α - lam ≠ 0 := sub_ne_zero.mpr (fun h => hlamS (h ▸ hα))
    rw [abs_div]
    have hpos : 0 < |α - lam| := abs_pos.mpr hαne
    calc |β - lam| / |α - lam| ≤ |α - lam| / |α - lam| := by
          apply div_le_div_of_nonneg_right (le_of_lt hlt) (le_of_lt hpos)
        _ = 1 := by rw [div_self (ne_of_gt hpos)]
  · exact moebiusCriticalValues_eq_empty _
  · exact MoebiusData.mapPoints_nonconstant (sepMoebius lam (β - lam) hβlam)

/-- Paper-scope 2.3 statement (Qbar/C form, named). -/
def Mobius23PaperScopeStatement : Prop :=
  ∀ emb : AlgebraicClosure ℚ →ₐ[ℚ] ℂ, QbarSeparationPaperStatement emb

/-- Layer A row: rational-version 2.3 Moebius separation. -/
def mobius23RowRationalProved : Mzk1LayerAConsumerActual.LayerARow :=
  { id := "MZK1.lemma24.layerA.mobius-2.3.rational"
    layer := "2.3 Moebius separation, rational version (P1/Moebius form)"
    status := Audit.VerificationStatus.proved
    formalRef := "Mzk1Lemma23SeparationActual.s3135_separation_rat; Mzk1Lemma23MoebiusActual.s3135_mobius_separation; sepMoebius; sepMoebius_mapPoints_finite/pole/infty; moebiusCriticalValues_eq_empty"
    gap := "paper-scope Qbar/C version remains named (Mobius23PaperScopeStatement); rational row does not close Qbar layer" }

/-- Status: rational 2.3 Moebius separation PROVED in P1 form; Qbar/C named; no closure. -/
def Moebius23Status : Audit.Obligation :=
  { id := "MZK1.lemma23.mobius"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.3 lines 163-165; Lead A398 assignment"
    status := Audit.VerificationStatus.interface
    note := "PROVED (rational P1/Moebius form): s3135_mobius_separation = for finite S subset Q, beta notin S there exist rational lam and C = beta - lam != 0 such that sepMoebius lam C (a=0,b=C,c=1,d=-lam, det = -C != 0) is a nonconstant P1 self-map with rational coefficients, N(beta) finite and != 0 (equals 1), N(alpha) finite for all alpha in S, |N(alpha)| = |C/(alpha-lam)| <= 1 on S, and no critical values. Supporting lemmas sepMoebius_mapPoints_finite/pole/infty. NAMED REMAINDER: Mobius23PaperScopeStatement (Qbar/C via Q-algebra embeddings). Layer A consumer mobius23Row keeps status interface; rational row mobius23RowRationalProved records the proved component. No closure; binding HOLD; gate NOT PASSED; registry frozen 14041."
    dependsOn := [ "MZK1.lemma23.separation", "MZK1.lemma24.layerA.consumer" ]
    sorryItems :=
      [ "Mobius23PaperScopeStatement (Qbar/C separation via embedding metric; named layer)",
        "upgrade of Layer A consumer mobius23Row at paper scope" ] }

open LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1CActual

/-- Base change of the rational separation Moebius map to the C-typed Moebius data. -/
def sepMoebiusC (lam C : ℚ) (hC : C ≠ 0) : Mzk1MoebiusP1CActual.MoebiusDataC :=
  Mzk1MoebiusP1CActual.mapToC (sepMoebius lam C hC)

/-- The value C/(emb x - lam) in C of the separation Moebius map at a Qbar point. -/
def moebiusValueC (emb : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) (lam C : ℚ) (x : AlgebraicClosure ℚ) : ℂ :=
  (C : ℂ) / ((emb x) - (lam : ℂ))

/-- **Paper-scope 2.3 in P1/Moebius form (Qbar/C, statement only)**: for a fixed
Q-algebra embedding of Qbar into C, every finite S in Qbar and beta outside S admit
rational lam, C (C != 0) such that lam is outside S and different from beta, the C-typed
Moebius map sepMoebiusC lam C has nonzero value at beta and the norm bounds
normSq(C/(x - lam)) <= 1 on S and <= normSq(value at beta). -/
def QbarSeparationMoebiusPaperStatement (emb : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) : Prop :=
  ∀ (S : Finset (AlgebraicClosure ℚ)) (β : AlgebraicClosure ℚ), β ∉ S →
    ∃ (lam C : ℚ) (hC : C ≠ 0),
      (algebraMap ℚ (AlgebraicClosure ℚ) lam) ∉ S ∧
      (algebraMap ℚ (AlgebraicClosure ℚ) lam) ≠ β ∧
      moebiusValueC emb lam C β ≠ 0 ∧
      (∀ α ∈ S, Complex.normSq (moebiusValueC emb lam C α) ≤ 1) ∧
      (∀ α ∈ S, Complex.normSq (moebiusValueC emb lam C α) ≤ Complex.normSq (moebiusValueC emb lam C β))

#check s3135_mobius_separation
#check mobius23RowRationalProved
end LeanFormal.IUT.XiFPaper.Mzk1Lemma23MoebiusActual
end