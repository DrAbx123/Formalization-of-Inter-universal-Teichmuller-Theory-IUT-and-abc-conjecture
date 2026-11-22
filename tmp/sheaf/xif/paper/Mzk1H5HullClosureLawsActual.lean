import tmp.sheaf.xif.paper.Hull09H5GapsActual

/-!
  Mainline: H5 hull closure laws derived from the tree hull=closure characterization
  (Hull09).  Real proofs only; the named class-B H5 gaps are untouched.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5HullClosureLawsActual

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Hull06DetTensorActual
open LeanFormal.IUT.XiFPaper.Hull09H5GapsActual

variable {l : PrimeGeFive} {V : Type uv}

/-- Every possible theta-pilot image lies in the source holomorphic hull. -/
theorem hull09_possibleThetaPilotImage_subset_hull
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.possibleThetaPilotImageSet v R n ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
  intro x hx
  rw [hull09_hull_eq_closure]
  exact Submonoid.subset_closure (Set.mem_union_left _ hx)

/-- The unit is in the hull. -/
theorem hull09_hull_one_mem
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (1 : I.ThetaPilotPoint v) ∈ I.sourceHolomorphicHull v R n := by
  rw [hull09_hull_eq_closure]
  exact Submonoid.one_mem _

/-- The hull is closed under multiplication (submonoid closure). -/
theorem hull09_hull_mul_mem
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {x y : I.ThetaPilotPoint v}
    (hx : x ∈ I.sourceHolomorphicHull v R n)
    (hy : y ∈ I.sourceHolomorphicHull v R n) :
    x * y ∈ I.sourceHolomorphicHull v R n := by
  rw [hull09_hull_eq_closure] at hx hy ⊢
  exact Submonoid.mul_mem _ hx hy

/-- The generating union (theta images and scaling units) lies in the hull. -/
theorem hull09_generators_subset_hull
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.possibleThetaPilotImageSet v R n ∪ I.sourceScalingUnits v ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
  rw [hull09_hull_eq_closure]
  exact Submonoid.subset_closure
/-- Powers of hull elements stay in the hull. -/
theorem hull09_hull_pow_mem
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {x : I.ThetaPilotPoint v} (hx : x ∈ I.sourceHolomorphicHull v R n) (k : Nat) :
    x ^ k ∈ I.sourceHolomorphicHull v R n := by
  induction k with
  | zero => simpa using hull09_hull_one_mem I v R n
  | succ k ih =>
      simpa [pow_succ] using hull09_hull_mul_mem I v R n ih hx
end LeanFormal.IUT.XiFPaper.Mzk1H5HullClosureLawsActual