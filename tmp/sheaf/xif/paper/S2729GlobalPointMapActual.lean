import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import tmp.sheaf.xif.paper.S2728NormLogProductActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2728NormLogProductActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2729GlobalPointMapActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The mixed-prime global carrier for the assembled point map. -/
abbrev S2729GlobalCarrier : Type :=
  (b : Bad (nativePlaceSelection T)) → qVFamTensorBlock T b

/-- The global point map assembled fiberwise from the actual per-b
`S2588PointMap`. -/
noncomputable def S2729GlobalPointMap (a n c : Nat) :
    S2729GlobalCarrier (l := l) T :=
  fun b => S2588PointMap (l := l) T b a n c

theorem S2729GlobalPointMap_apply (a n c : Nat)
    (b : Bad (nativePlaceSelection T)) :
    S2729GlobalPointMap (l := l) T a n c b =
      S2588PointMap (l := l) T b a n c :=
  rfl

/-- Global product norm: the product of the actual per-b S2588 point norms.
This is the product-form norm attached to the mixed-prime carrier, not a
single-place norm. -/
noncomputable def S2729GlobalPointNorm (a n c : Nat) : Real :=
  ∏ b : Bad (nativePlaceSelection T),
    ‖S2588PointMap (l := l) T b a n c‖

theorem S2729GlobalPointNorm_eq_prod (a n c : Nat) :
    S2729GlobalPointNorm (l := l) T a n c =
      ∏ b : Bad (nativePlaceSelection T),
        ‖S2588PointMap (l := l) T b a n c‖ :=
  rfl

/-- The global product norm is positive when every per-b norm is positive. -/
theorem S2729GlobalPointNorm_pos (a n c : Nat)
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < ‖S2588PointMap (l := l) T b a n c‖) :
    0 < S2729GlobalPointNorm (l := l) T a n c :=
  S2728_prod_pos _ hpos

/-- Log of the global product norm is the sum of the per-b logs. -/
theorem S2729_log_globalPointNorm_eq_sum (a n c : Nat)
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < ‖S2588PointMap (l := l) T b a n c‖) :
    Real.log (S2729GlobalPointNorm (l := l) T a n c) =
      ∑ b : Bad (nativePlaceSelection T),
        Real.log ‖S2588PointMap (l := l) T b a n c‖ :=
  S2728_log_prod _ hpos

/-- The negative global log is the sum of the per-b negative logs. -/
theorem S2729_neg_log_globalPointNorm_eq_sum (a n c : Nat)
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < ‖S2588PointMap (l := l) T b a n c‖) :
    -Real.log (S2729GlobalPointNorm (l := l) T a n c) =
      ∑ b : Bad (nativePlaceSelection T),
        -Real.log ‖S2588PointMap (l := l) T b a n c‖ :=
  S2728_neg_log_prod _ hpos

#check S2729GlobalPointMap
#print axioms S2729_neg_log_globalPointNorm_eq_sum

end LeanFormal.IUT.XiFPaper.S2729GlobalPointMapActual
end
