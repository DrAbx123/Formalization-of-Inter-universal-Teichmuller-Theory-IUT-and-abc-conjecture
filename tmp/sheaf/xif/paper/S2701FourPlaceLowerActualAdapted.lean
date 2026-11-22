import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2689SourceBadQAbsLogActual
import tmp.sheaf.xif.paper.S2699GenericQPilotRayActual
import tmp.sheaf.xif.paper.S2702FourPlaceDataActual

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2701FourPlaceLowerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2689SourceBadQAbsLogActual
open LeanFormal.IUT.XiFPaper.S2699GenericQPilotRayActual

local instance : Fact (Irreducible
    (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
open LeanFormal.IUT.XiFPaper.S2702FourPlaceDataActual

local instance s2701GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Residue-characteristic data needed for the lower bound: one place above
5 and one place above 2161. -/
structure S2701ResidueData (D : S2696FourPlaceData) : Prop where
  h5 : NumberFieldFinitePlace.residueCharacteristic D.p5a = 5
  h2161 : NumberFieldFinitePlace.residueCharacteristic D.p2161a = 2161

/-- The actual per-place bad-q absolute log on the four-place set. -/
noncomputable def S2701q (l : PrimeGeFive) (D : S2696FourPlaceData) :
    (p : NumberField.FinitePlace GaussianField) → p ∈ S2696Vbad D → Real :=
  fun p hp => |Real.log (badPlaceQProxy (S2696Selection l D) ⟨p, hp⟩)|

theorem S2701_five_mem (D : S2696FourPlaceData) :
    D.p5a ∈ S2696Vbad D := Or.inl rfl
theorem S2701_2161_mem (D : S2696FourPlaceData) :
    D.p2161a ∈ S2696Vbad D := Or.inr (Or.inr (Or.inl rfl))

theorem S2701_log_five_le (l : PrimeGeFive) (D : S2696FourPlaceData)
    (h : NumberFieldFinitePlace.residueCharacteristic D.p5a = 5) :
    Real.log 5 ≤ S2701q l D D.p5a (S2701_five_mem D) := by
  have hb := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696Selection l D) (⟨D.p5a, S2701_five_mem D⟩ : Bad (S2696Selection l D))
  have hb' : Real.log ((NumberFieldFinitePlace.residueCharacteristic D.p5a : Nat) : Real) ≤
      |Real.log (badPlaceQProxy (S2696Selection l D) ⟨D.p5a, S2701_five_mem D⟩)| := hb
  have hchar : ((NumberFieldFinitePlace.residueCharacteristic D.p5a : Nat) : Real) = 5 := by
    rw [h]; norm_num
  rw [hchar] at hb'
  simpa [S2701q] using hb'

theorem S2701_log_2161_le (l : PrimeGeFive) (D : S2696FourPlaceData)
    (h : NumberFieldFinitePlace.residueCharacteristic D.p2161a = 2161) :
    Real.log 2161 ≤ S2701q l D D.p2161a (S2701_2161_mem D) := by
  have hb := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696Selection l D) (⟨D.p2161a, S2701_2161_mem D⟩ : Bad (S2696Selection l D))
  have hb' : Real.log ((NumberFieldFinitePlace.residueCharacteristic D.p2161a : Nat) : Real) ≤
      |Real.log (badPlaceQProxy (S2696Selection l D) ⟨D.p2161a, S2701_2161_mem D⟩)| := hb
  have hchar : ((NumberFieldFinitePlace.residueCharacteristic D.p2161a : Nat) : Real) = 2161 := by
    rw [h]; norm_num
  rw [hchar] at hb'
  simpa [S2701q] using hb'

/-- Two-term lower bound: the full four-place sum is at least
`log 5 + log 2161`, using the 5-place and the 2161-place.  No pairwise
distinctness of the four places is needed. -/
theorem S2701_two_terms_le (l : PrimeGeFive) (D : S2696FourPlaceData)
    (hres : S2701ResidueData D) :
    Real.log 5 + Real.log 2161 ≤ S2696BadQAbsLog D (S2701q l D) := by
  classical
  unfold S2696BadQAbsLog
  letI : Fintype {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D} :=
    (S2696Vbad_finite D).fintype
  let a : {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D} :=
    ⟨D.p5a, S2701_five_mem D⟩
  let b : {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D} :=
    ⟨D.p2161a, S2701_2161_mem D⟩
  have hres_ne : NumberFieldFinitePlace.residueCharacteristic D.p5a ≠
      NumberFieldFinitePlace.residueCharacteristic D.p2161a := by
    rw [hres.h5, hres.h2161]; norm_num
  have hab : a ≠ b := by
    intro h
    exact hres_ne (congrArg
      (fun x : {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D} =>
        NumberFieldFinitePlace.residueCharacteristic x.1) h)
  have hnonneg : ∀ x : {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D},
      0 ≤ S2701q l D x.1 x.2 := fun x => abs_nonneg _
  have hpair : S2701q l D a.1 a.2 + S2701q l D b.1 b.2 ≤
      ∑ x : {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D},
        S2701q l D x.1 x.2 := by
    have hEq : (∑ x ∈ ({a, b} : Finset {p : NumberField.FinitePlace GaussianField //
        p ∈ S2696Vbad D}), S2701q l D x.1 x.2) =
        S2701q l D a.1 a.2 + S2701q l D b.1 b.2 :=
      Finset.sum_pair hab
    rw [← hEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro x _; exact Finset.mem_univ x)
      (by intro x _ _; exact hnonneg x)
  have h5 := S2701_log_five_le l D hres.h5
  have h2161 := S2701_log_2161_le l D hres.h2161
  linarith

/-- The lower bound needed by the q-pilot ray: `2 log 5 ≤ badQAbsLog`. -/
theorem S2701_two_log5_le (l : PrimeGeFive) (D : S2696FourPlaceData)
    (hres : S2701ResidueData D) :
    2 * Real.log 5 ≤ S2696BadQAbsLog D (S2701q l D) := by
  have h := S2701_two_terms_le l D hres
  have hlt : Real.log (5 : Real) < Real.log (2161 : Real) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- The canonical four-place actual data. -/
noncomputable def S2701D : S2696FourPlaceData := S2702FourPlaceData

theorem S2701D_residue : S2701ResidueData S2701D where
  h5 := by
    simpa [S2701D, S2702FourPlaceData] using S2702Place5a_residueCharacteristic
  h2161 := by
    simpa [S2701D, S2702FourPlaceData] using S2696GaussianPlace2161_residueCharacteristic

theorem S2701D_two_log5_le (l : PrimeGeFive) :
    2 * Real.log 5 ≤ S2696BadQAbsLog S2701D (S2701q l S2701D) :=
  S2701_two_log5_le l S2701D S2701D_residue

/-- q-pilot ray inclusion for the canonical four-place actual data. -/
theorem S2701_qPilot_mem_ray {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average = 2 * Real.log 5)
    (l : PrimeGeFive) :
    -(S2696BadQAbsLog S2701D (S2701q l S2701D)) ∈
      hullLogVolumeRay P.signedHullLogVolume :=
  S2699_qPilot_mem_ray_of_badQAbsLog_ge P hP _ (S2701D_two_log5_le l)

#check S2701_two_terms_le
#check S2701_two_log5_le
#check S2701D_residue
#check S2701D_two_log5_le
#check S2701_qPilot_mem_ray
#print axioms S2701D_two_log5_le
#print axioms S2701_qPilot_mem_ray

end LeanFormal.IUT.XiFPaper.S2701FourPlaceLowerActualAdapted
end
