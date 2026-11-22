import tmp.sheaf.xif.paper.S1632ThetaValueComparisonActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

/-!
# S1639: faithful theta scalar basic component

This file constructs the scalar-level theta data at a source point and label,
without using a weighted point divisor or an analytic theta value.

* `sourceThetaSectionValue I n m j` is the actual theta special value of the
  source Hodge theater at the point `(n,m)` and label `j`, read from the actual
  `FiniteThetaPacket.scale` carried by the original source input.
* `qvPowScalarMap q j` is the scalar map `q -> q ^ (j ^ 2)` into the real
  value field.  `thetaScalarMapAtPlace T b j` instantiates it at the actual
  native base q candidate `thetaBaseQReal T b`; hence it is exactly
  `q_v ^ (j ^ 2)`.
* `thetaScalarProduct T j` is the actual product `∏_b q_v ^ (j ^ 2)` over
  the bad places.
* `thetaNormalization I T n m j` is the explicit actual normalization
  `(q_source / ∏_b q_v) ^ (j ^ 2)`.
* `thetaValue_eq_product_mul_normalization` proves the comparison
  `thetaValue = ∏_b q_v ^ (j ^ 2) * normalization`.

The normalization is label-indexed.  This is forced by the formula: the
source theta value is `q_source ^ (j ^ 2)` while the product is
`(∏_b q_v) ^ (j ^ 2)`, so a single constant normalization would require
`q_source = ∏_b q_v`.

The q_v used here is the actual native base q candidate underlying S1632
(`thetaBaseQReal`).  This file does not assert that this candidate is the
elliptic-curve q-parameter, a 2l-th root, or that its product equals the source
theta value; those are the recorded identification gaps, not hidden
assumptions.

The exact source-vs-base-q identification
`thetaValue = ∏_b q_v ^ (j ^ 2)` is recorded as
`ThetaScalarIdentification` (equivalently, normalization equal to one).  It
is not asserted.  No placeholder proof, extra axiom, decision-procedure
gate, weighted point divisor, or analytic theta is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1639ThetaScalarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.S1632ThetaValueComparisonActual
open LeanFormal.IUT.Theorem311Source

universe v

variable {l : PrimeGeFive}
variable {V : Type v}
variable (I : OriginalInput l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The actual theta section value at a point and label -/

/-- The actual theta special value of the source Hodge theater at the point
`(n,m)` and label `j`. -/
noncomputable def sourceThetaSectionValue (n m : Int)
    (j : SignedLabel l.value) : Real :=
  (I.theaterAt n m).thetaPacket.scale j

theorem sourceThetaSectionValue_eq_packet_scale (n m : Int)
    (j : SignedLabel l.value) :
    sourceThetaSectionValue I n m j =
      (I.theaterAt n m).thetaPacket.scale j := rfl

theorem sourceThetaSectionValue_pos (n m : Int) (j : SignedLabel l.value) :
    0 < sourceThetaSectionValue I n m j :=
  (I.theaterAt n m).thetaPacket.scale_pos j

theorem sourceThetaSectionValue_ne_zero (n m : Int)
    (j : SignedLabel l.value) :
    sourceThetaSectionValue I n m j ≠ 0 :=
  ne_of_gt (sourceThetaSectionValue_pos I n m j)

/-- The actual source theta value is exactly the `j ^ 2`-th power of the
actual source q. -/
theorem sourceThetaSectionValue_eq_q_pow (n m : Int)
    (j : SignedLabel l.value) :
    sourceThetaSectionValue I n m j =
      ((I.theaterAt n m).thetaPacket.q) ^ (gaussExponent j.1).toNat := by
  unfold sourceThetaSectionValue
  rw [FiniteThetaPacket.scale_eq]
  rfl

/-- The actual theta section value packaged at a point and label.  The field
`value_eq_q_pow` records the source Gaussian power formula, not a
placeholder. -/
structure ThetaSectionValueObject (n m : Int) (j : SignedLabel l.value) where
  value : Real
  value_eq : value = sourceThetaSectionValue I n m j
  value_pos : 0 < value
  q : Real
  q_eq : q = (I.theaterAt n m).thetaPacket.q
  q_pos : 0 < q
  value_eq_q_pow : value = q ^ (gaussExponent j.1).toNat

noncomputable def thetaSectionValueObject (n m : Int)
    (j : SignedLabel l.value) :
    ThetaSectionValueObject I n m j where
  value := sourceThetaSectionValue I n m j
  value_eq := rfl
  value_pos := sourceThetaSectionValue_pos I n m j
  q := (I.theaterAt n m).thetaPacket.q
  q_eq := rfl
  q_pos := (I.theaterAt n m).thetaPacket.q_pos
  value_eq_q_pow := sourceThetaSectionValue_eq_q_pow I n m j

/-! ## 2. The scalar map `q_v -> q_v ^ (j ^ 2)` into the real value field -/

/-- Scalar map sending a q_v to its Gaussian label power `q_v ^ (j ^ 2)` in
the real value field. -/
noncomputable def qvPowScalarMap (q : Real)
    (j : SignedLabel l.value) : Real :=
  q ^ (gaussExponent j.1).toNat

theorem qvPowScalarMap_pos {q : Real} (hq : 0 < q)
    (j : SignedLabel l.value) : 0 < qvPowScalarMap q j :=
  pow_pos hq _

theorem qvPowScalarMap_ne_zero {q : Real} (hq : 0 < q)
    (j : SignedLabel l.value) : qvPowScalarMap q j ≠ 0 :=
  ne_of_gt (qvPowScalarMap_pos hq j)

/-- The actual source theta value is the scalar map at the source q, with
trivial local normalization. -/
theorem sourceThetaSectionValue_eq_qvPowScalarMap (n m : Int)
    (j : SignedLabel l.value) :
    sourceThetaSectionValue I n m j =
      qvPowScalarMap ((I.theaterAt n m).thetaPacket.q) j :=
  sourceThetaSectionValue_eq_q_pow I n m j

/-- The scalar map at a native bad place, `q_v ^ (j ^ 2)` in the real value
field. -/
noncomputable def thetaScalarMapAtPlace
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) : Real :=
  qvPowScalarMap (thetaBaseQReal T b) j

theorem thetaScalarMapAtPlace_eq
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    thetaScalarMapAtPlace T b j =
      (thetaBaseQReal T b) ^ (gaussExponent j.1).toNat := rfl

theorem thetaScalarMapAtPlace_eq_thetaScalarMap
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    thetaScalarMapAtPlace T b j = thetaScalarMap T b j := rfl

theorem thetaScalarMapAtPlace_pos
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    0 < thetaScalarMapAtPlace T b j :=
  qvPowScalarMap_pos (thetaBaseQReal_pos T b) j

/-- The actual base q product over all bad places. -/
noncomputable def baseQProduct : Real :=
  ∏ b : Bad (nativePlaceSelection T), thetaBaseQReal T b

theorem baseQProduct_pos : 0 < baseQProduct T :=
  Finset.prod_pos (fun b _ => thetaBaseQReal_pos T b)

theorem baseQProduct_ne_zero : baseQProduct T ≠ 0 :=
  ne_of_gt (baseQProduct_pos T)

/-! ## 3. The product `∏_b q_v ^ (j ^ 2)` and its power formula -/

/-- The actual product over the bad places of `q_v ^ (j ^ 2)`. -/
noncomputable def thetaScalarProduct (j : SignedLabel l.value) : Real :=
  ∏ b : Bad (nativePlaceSelection T), thetaScalarMapAtPlace T b j

/-- The constructed product is definitionally S1632's product. -/
theorem thetaScalarProduct_eq_thetaProductValue
    (j : SignedLabel l.value) :
    thetaScalarProduct T j = thetaProductValue T j := rfl

theorem thetaScalarProduct_pos (j : SignedLabel l.value) :
    0 < thetaScalarProduct T j :=
  Finset.prod_pos (fun b _ => thetaScalarMapAtPlace_pos T b j)

theorem thetaScalarProduct_ne_zero (j : SignedLabel l.value) :
    thetaScalarProduct T j ≠ 0 :=
  ne_of_gt (thetaScalarProduct_pos T j)

/-- The product of the `q_v ^ (j ^ 2)` is the `j ^ 2`-th power of the base
q product. -/
theorem thetaScalarProduct_eq_baseQProduct_pow
    (j : SignedLabel l.value) :
    thetaScalarProduct T j =
      (baseQProduct T) ^ (gaussExponent j.1).toNat := by
  unfold thetaScalarProduct thetaScalarMapAtPlace qvPowScalarMap baseQProduct
  rw [Finset.prod_pow]

/-! ## 4. The explicit normalization and the comparison theorem -/

/-- The explicit actual normalization at a point and label:
`(q_source / ∏_b q_v) ^ (j ^ 2)`. -/
noncomputable def thetaNormalization (n m : Int)
    (j : SignedLabel l.value) : Real :=
  (((I.theaterAt n m).thetaPacket.q) / baseQProduct T) ^
    (gaussExponent j.1).toNat

theorem thetaNormalization_pos (n m : Int) (j : SignedLabel l.value) :
    0 < thetaNormalization I T n m j := by
  unfold thetaNormalization
  exact pow_pos
    (div_pos (I.theaterAt n m).thetaPacket.q_pos (baseQProduct_pos T)) _

theorem thetaNormalization_ne_zero (n m : Int)
    (j : SignedLabel l.value) :
    thetaNormalization I T n m j ≠ 0 :=
  ne_of_gt (thetaNormalization_pos I T n m j)

/-- The explicit normalization is the actual ratio of the theta section value
to the actual `q_v ^ (j ^ 2)` product. -/
theorem thetaNormalization_eq_ratio (n m : Int)
    (j : SignedLabel l.value) :
    thetaNormalization I T n m j =
      sourceThetaSectionValue I n m j / thetaScalarProduct T j := by
  unfold thetaNormalization
  rw [sourceThetaSectionValue_eq_q_pow I n m j,
    thetaScalarProduct_eq_baseQProduct_pow T j, div_pow]

/-- **The faithful scalar comparison**: the actual theta section value is the
actual product of `q_v ^ (j ^ 2)` times the explicitly constructed
normalization. -/
theorem thetaValue_eq_product_mul_normalization (n m : Int)
    (j : SignedLabel l.value) :
    sourceThetaSectionValue I n m j =
      thetaScalarProduct T j * thetaNormalization I T n m j := by
  rw [sourceThetaSectionValue_eq_q_pow I n m j,
    thetaScalarProduct_eq_baseQProduct_pow T j]
  unfold thetaNormalization
  rw [div_pow]
  have hp : baseQProduct T ≠ 0 := baseQProduct_ne_zero T
  field_simp [hp]

theorem thetaValue_eq_normalization_mul_product (n m : Int)
    (j : SignedLabel l.value) :
    sourceThetaSectionValue I n m j =
      thetaNormalization I T n m j * thetaScalarProduct T j := by
  rw [thetaValue_eq_product_mul_normalization I T n m j, mul_comm]

/-- The exact source-vs-base-q identification whose proof is not asserted:
the actual theta section value equals the bare product of
`q_v ^ (j ^ 2)`. -/
def ThetaScalarIdentification (n m : Int)
    (j : SignedLabel l.value) : Prop :=
  sourceThetaSectionValue I n m j = thetaScalarProduct T j

theorem thetaScalarIdentification_iff_normalization_eq_one
    (n m : Int) (j : SignedLabel l.value) :
    ThetaScalarIdentification I T n m j ↔
      thetaNormalization I T n m j = 1 := by
  constructor
  · intro h
    rw [thetaNormalization_eq_ratio I T n m j, h,
      div_self (thetaScalarProduct_ne_zero T j)]
  · intro h
    unfold ThetaScalarIdentification
    calc
      sourceThetaSectionValue I n m j =
          thetaScalarProduct T j * thetaNormalization I T n m j :=
        thetaValue_eq_product_mul_normalization I T n m j
      _ = thetaScalarProduct T j * 1 := by rw [h]
      _ = thetaScalarProduct T j := by ring

/-- The all-labels form of the exact identification. -/
def ThetaScalarIdentificationAll (n m : Int) : Prop :=
  ∀ j : SignedLabel l.value, ThetaScalarIdentification I T n m j

theorem thetaScalarIdentificationAll_iff_normalization_eq_one
    (n m : Int) :
    ThetaScalarIdentificationAll I T n m ↔
      ∀ j : SignedLabel l.value, thetaNormalization I T n m j = 1 := by
  constructor
  · intro h j
    exact (thetaScalarIdentification_iff_normalization_eq_one
      I T n m j).mp (h j)
  · intro h j
    exact (thetaScalarIdentification_iff_normalization_eq_one
      I T n m j).mpr (h j)

/-! ## 5. The packaged actual scalar-comparison data -/

/-- Actual scalar-comparison data at one point and label. -/
structure ThetaScalarComparison (n m : Int)
    (j : SignedLabel l.value) where
  thetaValue : Real
  thetaValue_eq : thetaValue = sourceThetaSectionValue I n m j
  scalarMap : Bad (nativePlaceSelection T) → Real
  scalarMap_eq : ∀ b, scalarMap b = thetaScalarMapAtPlace T b j
  product : Real
  product_eq : product = thetaScalarProduct T j
  normalization : Real
  normalization_eq : normalization = thetaNormalization I T n m j
  normalization_ne_zero : normalization ≠ 0
  comparison : thetaValue = product * normalization

noncomputable def thetaScalarComparison (n m : Int)
    (j : SignedLabel l.value) :
    ThetaScalarComparison I T n m j where
  thetaValue := sourceThetaSectionValue I n m j
  thetaValue_eq := rfl
  scalarMap := fun b => thetaScalarMapAtPlace T b j
  scalarMap_eq := fun _ => rfl
  product := thetaScalarProduct T j
  product_eq := rfl
  normalization := thetaNormalization I T n m j
  normalization_eq := rfl
  normalization_ne_zero := thetaNormalization_ne_zero I T n m j
  comparison := thetaValue_eq_product_mul_normalization I T n m j

/-- Actual scalar-comparison data for all labels at one source point. -/
structure ThetaScalarFamily (n m : Int) where
  thetaValue : SignedLabel l.value → Real
  thetaValue_eq : ∀ j, thetaValue j = sourceThetaSectionValue I n m j
  scalarMap : Bad (nativePlaceSelection T) → SignedLabel l.value → Real
  scalarMap_eq : ∀ b j, scalarMap b j = thetaScalarMapAtPlace T b j
  product : SignedLabel l.value → Real
  product_eq : ∀ j, product j = thetaScalarProduct T j
  normalization : SignedLabel l.value → Real
  normalization_eq : ∀ j, normalization j = thetaNormalization I T n m j
  normalization_ne_zero : ∀ j, normalization j ≠ 0
  comparison : ∀ j, thetaValue j = product j * normalization j

noncomputable def thetaScalarFamily (n m : Int) :
    ThetaScalarFamily I T n m where
  thetaValue := sourceThetaSectionValue I n m
  thetaValue_eq := fun _ => rfl
  scalarMap := fun b j => thetaScalarMapAtPlace T b j
  scalarMap_eq := fun _ _ => rfl
  product := thetaScalarProduct T
  product_eq := fun _ => rfl
  normalization := thetaNormalization I T n m
  normalization_eq := fun _ => rfl
  normalization_ne_zero := thetaNormalization_ne_zero I T n m
  comparison := thetaValue_eq_product_mul_normalization I T n m

end LeanFormal.IUT.XiFPaper.S1639ThetaScalarActual
