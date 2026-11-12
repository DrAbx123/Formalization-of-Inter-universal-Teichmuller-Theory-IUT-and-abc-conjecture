# OUR-TARGET-GEOM-LEMMAS — local O-inclusion, tensor monotonicity, normalized Haar (A1122)

Status: lemma plan; no compile.

## 1. Local green lemma

- integers_subset_integralLogShell
  namespace: LeanFormal.IUT.LocalFieldLogarithm
  file: LeanFormal/IUT/Foundations/LocalFields/LogarithmLocalInverse.lean:120
  statement:
    (Integers K : Set K) subset (integralLogShell (K := K) (p := p) : Set K)
  status: PROVED (green).
- Integers is
  LeanFormal.IUT.LocalFieldIntegralUnits.Integers K
  = (NormedField.valuation (K := K)).integer
  (IntegralUnits.lean:25).
- actualC3LogShellL_eq_integralLogShell
  (Mzk1C3LogShellTensorLActual:70):
    actualC3LogShellL i = (integralLogShell ... : Set (C3LogShellFiberL i)).
  status: PROVED.

## 2. tensorIntegralRegion monotonicity

Definition (FinitePadicTensorIntegralRegion:20):
  tensorIntegralRegion (p := p) (M := M) S
    = finitePadicTensorTprod '' (Set.pi Set.univ S).

No existing tensorIntegralRegion_mono; it is immediate from image/pi monotonicity:

theorem tensorIntegralRegion_mono
    {ι : Type} [Fintype ι] {p : Nat} [Fact p.Prime]
    {M : ι -> Type*} [forall i, NormedAddCommGroup (M i)]
    [forall i, NormedSpace ℚ_[p] (M i)]
    {S T : (i : ι) -> Set (M i)} (h : forall i, S i subset T i) :
    tensorIntegralRegion (p := p) M S subset tensorIntegralRegion (p := p) M T := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, fun i _ => h i (hx i (Set.mem_univ i)), rfl⟩

Status: PROVABLE (no missing math; only Set.pi/image membership).

## 3. The integral tensor region and its inclusion

Define the tensor image of the product of local integer rings:

noncomputable def tensorIntegerRegionL :
    Set (C3LogShellTensorBlockL (I := I) C3L) :=
  tensorIntegralRegion (p := C3L.p)
    (M := fun i => C3LogShellFiberL (I := I) C3L i)
    (fun i => (LeanFormal.IUT.LocalFieldIntegralUnits.Integers
      (C3LogShellFiberL (I := I) C3L i) : Set _))

Then:

theorem tensorIntegerRegionL_subset_actual :
    tensorIntegerRegionL (I := I) C3L subset
      actualC3LogShellTensorRegionL (I := I) C3L := by
  apply tensorIntegralRegion_mono
  intro i
  rw [actualC3LogShellL_eq_integralLogShell]
  exact LeanFormal.IUT.LocalFieldLogarithm.integers_subset_integralLogShell

Status: PROVABLE after tensorIntegralRegion_mono and the green local inclusion.

## 4. Normalization mu(tensorIntegralRegion O) = 1

The raw actualC3LogShellTensorHaarL = Measure.addHaar is not normalized.
To impose mu(tensor O) = 1 we need either:

(A) A normalized measure definition:
noncomputable def normalizedTensorHaarL (hpos : 0 < mu (tensorIntegerRegionL) )
    (hfin : mu (tensorIntegerRegionL) < top) :
    Measure (C3LogShellTensorBlockL ...) :=
  (mu (tensorIntegerRegionL)).toReal⁻¹ • mu

with the scalar nonzero. Then
  normalizedTensorHaarL (tensorIntegerRegionL) = 1
is immediate from smul_apply and toReal inverse, given 0 < mu < top.

(B) A structure carrying the normalization as data:
structure NormalizedTensorHaarData where
  mu : Measure (C3LogShellTensorBlockL ...)
  isAddHaar : Measure.IsAddHaarMeasure mu
  mass_integer_region : mu (tensorIntegerRegionL) = 1

Needed to make (A) real:
- positivity: 0 < mu (tensorIntegerRegionL);
- finiteness: mu (tensorIntegerRegionL) < top;
- these follow if tensorIntegerRegionL has nonempty interior and is compact.
  No such lemma for the tensor image exists in the tree (only compactness of
  actualC3LogShellTensorRegionL is proved). This is the exact GAP.

## 5. Consequences under the normalization

Assume D : NormalizedTensorHaarData (so mu(tensor O)=1).

lemma haar_actual_ge_one :
    1 <= D.mu (actualC3LogShellTensorRegionL) := by
  rw [<- D.mass_integer_region]
  exact measure_mono (tensorIntegerRegionL_subset_actual ...)

Then, with R = - log (D.mu actualRegion) (normalized analogue of S2807):
  R <= 0
because log(D.mu actualRegion) >= log 1 = 0.

Finally, with A = absLogQ >= 0:
  M = A - R >= A >= 0.

Status:
- haar_actual_ge_one: PROVABLE from measure_mono + normalization;
- R_nonpos: PROVABLE from log_nonneg + ge_one;
- M_nonneg: PROVABLE by linarith with A>=0.

## 6. Lean lemma checklist for Mzk1OurAccurateTargetActual

Import:
- tmp.sheaf.xif.paper.Mzk1C3LogShellTensorLActual
- LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse
- LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorIntegralRegion
- Mathlib.Tactic

Declarations:
1. tensorIntegralRegion_mono            PROVABLE (image/pi monotonicity)
2. tensorIntegerRegionL                 DEF
3. tensorIntegerRegionL_subset_actual  PROVABLE (1 + green local inclusion)
4. NormalizedTensorHaarData            DEF (mass_integer_region field)
   or normalizedTensorHaarL            DEF + normalization lemma
5. haar_actual_ge_one                  PROVABLE from 3,4, measure_mono
6. R_nonpos_of_normalized              PROVABLE from 5, log_nonneg
7. M_nonneg_of_normalized              PROVABLE from 6 and A>=0

Exact GAP:
- positivity/finiteness of mu(tensorIntegerRegionL) (nonempty interior/compact
  tensor image), needed to define normalizedTensorHaarL without a carried field;
- identification of the normalized mu with the raw S2807 Haar (only up to the
  scalar mu(tensor O));
- no theorem currently connects S2717ThetaHullLogVolume to this normalized
  measure; S2807 uses raw addHaar.

## 7. Verdict

- Local inclusion and tensor monotonicity are fully provable from green lemmas.
- The region inclusion tensor O subset actualRegion is provable.
- With a normalized Haar (mass tensor O = 1), Haar(actualRegion) >= 1,
  hence R <= 0 and M = A - R >= A >= 0.
- The only missing geometric input is the normalization/existence of
  mu(tensor O) (positive finite) and its identification with the S2807 raw
  Haar. No fake normalization is introduced.
