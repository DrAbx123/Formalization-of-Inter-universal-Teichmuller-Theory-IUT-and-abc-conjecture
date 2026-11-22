import tmp.sheaf.n8.closure.EtaAnabAtFPlace
import Mathlib

/-!
# Eta Rss as an equal-volume region quotient

`Rss` is the quotient of actual F-completion regions by equality of additive
Haar volume.  The fixed log-shell is only a donor point in this quotient; the
readout descends to the quotient.  At least two actual regions with different
volume are constructed, so the quotient is not a subsingleton.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace

namespace LeanFormal.IUT.N8Closure.EtaRegionQuotientRss

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual F-completion carrier of the native F-place. -/
abbrev K : Type := CommonPrimeCompletion (K := X.S.arithmetic.F) (nativeFPlaceAtPrime X)

variable [MeasurableSpace (K X)] [BorelSpace (K X)]
variable (mu : Measure (K X)) [Measure.IsAddHaarMeasure mu]
variable [Measure.IsOpenPosMeasure mu]

abbrev Region : Type := Set (K X)

/-- Regions are identified exactly when their actual Haar volumes agree. -/
def RegionSetoid : Setoid (Region X) where
  r R S := mu R = mu S
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

abbrev Rss : Type := Quotient (RegionSetoid (X := X) (mu := mu))

def rssOf (R : Region X) : Rss (X := X) (mu := mu) :=
  Quotient.mk (RegionSetoid (X := X) (mu := mu)) R

/-- The volume readout descends to the equal-volume quotient. -/
noncomputable def readout (q : Rss (X := X) (mu := mu)) : ENNReal :=
  Quotient.lift (fun R : Region X => mu R)
    (fun _ _ h => h) q

theorem readout_mk (R : Region X) :
    readout (X := X) (mu := mu) (rssOf (X := X) (mu := mu) R) = mu R := rfl

theorem rssOf_ne_of_volume_ne {R S : Region X} (h : mu R ≠ mu S) :
    rssOf (X := X) (mu := mu) R ≠ rssOf (X := X) (mu := mu) S := by
  intro hq
  exact h (Quotient.exact hq)

/-- Two actual regions with different volumes: empty and full. -/
theorem exists_two_regions_diff_volume :
    ∃ R S : Region X, mu R ≠ mu S := by
  refine ⟨∅, Set.univ, ?_⟩
  have hzero : mu (∅ : Region X) = 0 := measure_empty
  have hpos : 0 < mu (Set.univ : Region X) := by
    refine Measure.measure_pos_of_nonempty_interior mu ⟨(0 : K X), ?_⟩
    simp
  intro hEq
  have : mu (Set.univ : Region X) = 0 := by simpa [hzero] using hEq.symm
  exact (ne_of_gt hpos) this

/-- The equal-volume quotient is not a subsingleton: the empty and full
regions have different volumes. -/
theorem rss_not_subsingleton : ¬ Subsingleton (Rss (X := X) (mu := mu)) := by
  intro hsub
  have hq : rssOf (X := X) (mu := mu) (∅ : Region X) =
      rssOf (X := X) (mu := mu) (Set.univ : Region X) := Subsingleton.elim _ _
  have hvol : mu (∅ : Region X) = mu (Set.univ : Region X) := Quotient.exact hq
  have hzero : mu (∅ : Region X) = 0 := measure_empty
  have hpos : 0 < mu (Set.univ : Region X) := by
    refine Measure.measure_pos_of_nonempty_interior mu ⟨(0 : K X), ?_⟩
    simp
  have : mu (Set.univ : Region X) = 0 := by simpa [hzero] using hvol.symm
  exact (ne_of_gt hpos) this

/-- The fixed F log-shell is a donor region in the quotient, not the Rss
definition. -/
def fixedShellDonor : Region X :=
  (localShellAtF X).logShell

theorem fixedShellDonor_readout :
    readout (X := X) (mu := mu) (rssOf (X := X) (mu := mu) (fixedShellDonor X)) =
      mu (fixedShellDonor X) := rfl

end LeanFormal.IUT.N8Closure.EtaRegionQuotientRss
