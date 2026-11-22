import tmp.sheaf.xif.paper.S1327Ind3IntegralLogShellActual

/-!
# S1427: the exact place comparison for the integral Ind3 carrier

## What S1327 leaves open

S1327 constructs the genuine integral Ind3 log-shell carrier over the actual
place type IntegralPlaceTotal I = (vQ, v).  At the ambient source place type V
of OriginalInput, its first field is the exact place comparison

  IntegralInd3PlaceComparison I = V -> IntegralPlaceTotal I.

S1327 proves that *given* such a comparison the induced carrier has first field

  shell i v = integralShell I (p v).1 (p v).2  (rfl),

but it constructs no inhabitant of the comparison and explicitly refuses an
arbitrary constant place map.

## What is proved here

1. The comparison is *exactly* a source finite-place index map.  There is a
   canonical equivalence

     IntegralInd3PlaceComparison I ~= (V -> NumberField.FinitePlace Fmod)

   where Fmod = I.initial.arithmetic.Fmod.  Forward direction: read the actual
   finite place (p v).2.1.  Backward direction: map a source finite place w
   to (completionRationalPrime w, <w, rfl>).  The nontrivial direction is the
   round trip, proved by Sigma.subtype_ext: the rational valuation is
   determined by the finite place because actualIntegralPlace I vQ is the
   subtype of finite places whose completionRationalPrime is vQ.1.

   Consequently

     IntegralInd3PlaceComparisonRequired I <-> Nonempty (V -> FinitePlace Fmod),

   so the exact first missing field is a genuine source finite-place index map,
   not an extra structure and not a Q-vector-space carrier.

2. For every supplied source finite-place index map f : V -> FinitePlace Fmod,
   the actual carrier is constructed:

     carrierOfSourceFinitePlaceIndex I j f :=
        integralInd3LogShellCarrierOfMap I j (comparisonOfFinitePlaceIndex I f).

   Its first field is proved definitionally equal to the actual integral
   log-shell at the selected source place:

     shell i v = integralShell I (completionRationalPrime (f v)) <f v, rfl>,

   and also equal to the subtype carrier of actualIntegralLogShell.  The
   shell contains 1, is nontrivial, has the whole local field as Q_p-span, is
   not the whole local field, and is not closed under rational or p^{-1}
   scalars.  Thus the carrier is the integral Z-lattice of S1313, not an
   IQSpan/Q-vector surrogate.

3. The V-indexed Ind3 stage datum of S1327 is filled from f, with exact first
   field and exact stage projections.

## Exact gap for the general source place type

OriginalInput has no field V -> NumberField.FinitePlace Fmod; its V is an
arbitrary type and the selected/bad source place types are opaque fields of
SourceDefinition31Data.  Therefore no comparison is constructed here for a
general I; a source finite-place index map is the exact missing datum.  No
constant map, no Classical.choice place selection, no Nonempty gate and no
IQSpan/Q-vector carrier is used.

-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1427Ind3PlaceComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual
open LeanFormal.IUT.XiFPaper.S1313IntegralLogShellContractActual
open LeanFormal.IUT.XiFPaper.S1327Ind3IntegralLogShellActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The exact source finite-place index -/

/-- The source finite-place index map: the exact datum equivalent to S1327's
place comparison V -> (vQ, v). -/
abbrev SourceFinitePlaceIndex : Type (max uv (max 0 ua)) :=
  V → NumberField.FinitePlace I.initial.arithmetic.Fmod

/-- The canonical comparison associated with a source finite-place index map.
The rational valuation is the actual rational prime under the finite place. -/
noncomputable def comparisonOfFinitePlaceIndex
    (f : SourceFinitePlaceIndex I) : IntegralInd3PlaceComparison I :=
  fun v => ⟨completionRationalPrime (f v), ⟨f v, rfl⟩⟩

/-- The first component of the comparison is the rational prime under the
source finite place. -/
@[simp] theorem comparisonOfFinitePlaceIndex_fst
    (f : SourceFinitePlaceIndex I) (v : V) :
    (comparisonOfFinitePlaceIndex I f v).1 = completionRationalPrime (f v) :=
  rfl

/-- The actual finite place of the comparison is the supplied source finite
place. -/
@[simp] theorem comparisonOfFinitePlaceIndex_snd_val
    (f : SourceFinitePlaceIndex I) (v : V) :
    ((comparisonOfFinitePlaceIndex I f v).2).val = f v :=
  rfl

/-- The source finite-place index underlying a comparison: the actual finite
place of each pair. -/
def finitePlaceIndexOfComparison
    (p : IntegralInd3PlaceComparison I) : SourceFinitePlaceIndex I :=
  fun v => (p v).2.1

/-- Every actual place is determined by its finite place: the rational
valuation is completionRationalPrime of the finite place.  This is the
nontrivial round-trip identity of the equivalence below. -/
theorem sigma_mk_eq_self (x : IntegralPlaceTotal I) :
    (⟨completionRationalPrime x.2.1,
        (⟨x.2.1, rfl⟩ :
          actualIntegralPlace I (completionRationalPrime x.2.1))⟩ :
      IntegralPlaceTotal I) = x := by
  refine Sigma.subtype_ext ?_ ?_
  · exact Subtype.ext x.2.2
  · rfl

/-- The forward-backward round trip on comparisons is the identity. -/
theorem comparisonOfFinitePlaceIndex_finitePlaceIndexOfComparison
    (p : IntegralInd3PlaceComparison I) :
    comparisonOfFinitePlaceIndex I (finitePlaceIndexOfComparison I p) = p := by
  funext v
  exact sigma_mk_eq_self I (p v)

/-- The backward-forward round trip on source finite-place index maps is the
identity. -/
theorem finitePlaceIndexOfComparison_comparisonOfFinitePlaceIndex
    (f : SourceFinitePlaceIndex I) :
    finitePlaceIndexOfComparison I (comparisonOfFinitePlaceIndex I f) = f := by
  funext v
  rfl

/-- The exact equivalence: S1327's place comparison is exactly a V-indexed
source finite-place map. -/
noncomputable def comparisonEquivSourceFinitePlaceIndex :
    IntegralInd3PlaceComparison I ≃ SourceFinitePlaceIndex I where
  toFun := finitePlaceIndexOfComparison I
  invFun := comparisonOfFinitePlaceIndex I
  left_inv := comparisonOfFinitePlaceIndex_finitePlaceIndexOfComparison I
  right_inv := finitePlaceIndexOfComparison_comparisonOfFinitePlaceIndex I

/-- Exactness of the required first field: an inhabitant of S1327's
IntegralInd3PlaceComparisonRequired is exactly a source finite-place index
map.  No Q-vector-space or span data is involved. -/
theorem integralInd3PlaceComparisonRequired_iff_sourceFinitePlaceIndex :
    IntegralInd3PlaceComparisonRequired I ↔
      Nonempty (SourceFinitePlaceIndex I) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨finitePlaceIndexOfComparison I p⟩
  · rintro ⟨f⟩
    exact ⟨comparisonOfFinitePlaceIndex I f⟩

/-! ## 2. The exact first field of the integral carrier -/

/-- The actual V-indexed integral Ind3 log-shell carrier built from a supplied
source finite-place index map. -/
noncomputable def carrierOfSourceFinitePlaceIndex (j : Nat)
    (f : SourceFinitePlaceIndex I) :
    Ind3LogShellCarrier.{uv, 0, ua} (V := V) (R := ℤ) j :=
  integralInd3LogShellCarrierOfMap I j (comparisonOfFinitePlaceIndex I f)

/-- The first field of the carrier is exactly the actual integral log-shell at
the selected source finite place. -/
theorem carrierOfSourceFinitePlaceIndex_shell (j : Nat)
    (f : SourceFinitePlaceIndex I) (i : Capsule j) (v : V) :
    (carrierOfSourceFinitePlaceIndex I j f).shell i v =
      integralShell I (completionRationalPrime (f v)) ⟨f v, rfl⟩ :=
  rfl

/-- The first field is the subtype carrier of S1313's actual integral
log-shell. -/
theorem carrierOfSourceFinitePlaceIndex_shell_eq_actual (j : Nat)
    (f : SourceFinitePlaceIndex I) (i : Capsule j) (v : V) :
    (carrierOfSourceFinitePlaceIndex I j f).shell i v =
      ↥(actualIntegralLogShell I (completionRationalPrime (f v)) ⟨f v, rfl⟩) :=
  rfl

/-- The V-indexed carrier closes S1266's open carrier requirement at V once a
source finite-place index map is supplied. -/
theorem carrierRequired_of_sourceFinitePlaceIndex (j : Nat)
    (f : SourceFinitePlaceIndex I) :
    Ind3LogShellCarrierRequired.{uv, 0, ua} (V := V) (R := ℤ) j :=
  ind3LogShellCarrierRequired_of_integralPlaceMap I j
    (comparisonOfFinitePlaceIndex I f)

/-! ## 3. The selected shell is integral, not an IQSpan/Q-vector -/

/-- The selected shell contains 1, so it is a nonzero integral lattice. -/
theorem carrierOfSourceFinitePlaceIndex_shell_one_mem (j : Nat)
    (f : SourceFinitePlaceIndex I) (i : Capsule j) (v : V) :
    (1 : CommonPrimeCompletion ⟨f v, rfl⟩) ∈
      actualIntegralLogShell I (completionRationalPrime (f v)) ⟨f v, rfl⟩ :=
  one_mem_integralShell I _ _

/-- The selected shell is nontrivial: it is not the one-point model. -/
theorem carrierOfSourceFinitePlaceIndex_shell_nontrivial (j : Nat)
    (f : SourceFinitePlaceIndex I) (i : Capsule j) (v : V) :
    Nontrivial ((carrierOfSourceFinitePlaceIndex I j f).shell i v) :=
  integralShell_nontrivial I (completionRationalPrime (f v)) ⟨f v, rfl⟩

/-- The selected shell is not the whole local field. -/
theorem carrierOfSourceFinitePlaceIndex_shell_ne_univ (j : Nat)
    (f : SourceFinitePlaceIndex I) (i : Capsule j) (v : V) :
    (actualIntegralLogShell I (completionRationalPrime (f v)) ⟨f v, rfl⟩ :
      Set (CommonPrimeCompletion ⟨f v, rfl⟩)) ≠ Set.univ :=
  integralShell_ne_univ I (completionRationalPrime (f v)) ⟨f v, rfl⟩

/-- The selected shell's Q_p-span is the whole local field. -/
theorem carrierOfSourceFinitePlaceIndex_shell_span_padic_eq_top (j : Nat)
    (f : SourceFinitePlaceIndex I) (i : Capsule j) (v : V) :
    Submodule.span ℚ_[(completionRationalPrime (f v)).val]
      (actualIntegralLogShell I (completionRationalPrime (f v)) ⟨f v, rfl⟩ :
        Set (CommonPrimeCompletion ⟨f v, rfl⟩)) = ⊤ :=
  integralShell_span_padic_eq_top I (completionRationalPrime (f v)) ⟨f v, rfl⟩

/-- The selected shell is not closed under division by its residue prime: it
is an integral Z_p-lattice, not a Q_p-vector space. -/
theorem carrierOfSourceFinitePlaceIndex_shell_not_smul_inv_closed (j : Nat)
    (f : SourceFinitePlaceIndex I) (i : Capsule j) (v : V) :
    ¬ (∀ x ∈ actualIntegralLogShell I (completionRationalPrime (f v)) ⟨f v, rfl⟩,
        ((completionRationalPrime (f v)).val : ℚ_[(completionRationalPrime (f v)).val])⁻¹ •
          x ∈ actualIntegralLogShell I (completionRationalPrime (f v)) ⟨f v, rfl⟩) :=
  integralShell_not_smul_inv_closed I _ _

/-- The selected shell is not closed under all rational scalars: it is not a
Q-vector space.  This is the precise sense in which the carrier is not the
IQSpan used by S1270. -/
theorem carrierOfSourceFinitePlaceIndex_shell_not_rat_smul_closed (j : Nat)
    (f : SourceFinitePlaceIndex I) (i : Capsule j) (v : V) :
    ¬ (∀ (q : ℚ)
        (x : CommonPrimeCompletion ⟨f v, rfl⟩),
        x ∈ actualIntegralLogShell I (completionRationalPrime (f v)) ⟨f v, rfl⟩ →
          q • x ∈ actualIntegralLogShell I (completionRationalPrime (f v)) ⟨f v, rfl⟩) :=
  integralShell_not_rat_smul_closed I _ _

/-! ## 4. The V-indexed Ind3 stage datum -/

/-- The V-indexed integral Ind3 stage datum with the exact first field from a
source finite-place index map. -/
noncomputable def stageDatumOfSourceFinitePlaceIndex
    (f : SourceFinitePlaceIndex I) (n : Int) (j : Nat) :
    IntegralInd3StageDatumAtV I (comparisonOfFinitePlaceIndex I f) n j :=
  integralInd3StageDatumAtV I (comparisonOfFinitePlaceIndex I f) n j

/-- The datum's first field is exactly the carrier built from f. -/
@[simp] theorem stageDatumOfSourceFinitePlaceIndex_logShell
    (f : SourceFinitePlaceIndex I) (n : Int) (j : Nat) :
    (stageDatumOfSourceFinitePlaceIndex I f n j).logShell =
      carrierOfSourceFinitePlaceIndex I j f :=
  rfl

/-- The datum's first field at a capsule label and source place is exactly the
actual integral log-shell at the selected source finite place. -/
@[simp] theorem stageDatumOfSourceFinitePlaceIndex_shell
    (f : SourceFinitePlaceIndex I) (n : Int) (j : Nat)
    (i : Capsule j) (v : V) :
    (stageDatumOfSourceFinitePlaceIndex I f n j).logShell.shell i v =
      integralShell I (completionRationalPrime (f v)) ⟨f v, rfl⟩ :=
  rfl

/-- The stage data of the datum are S1266's actual times-mu stage data. -/
@[simp] theorem stageDatumOfSourceFinitePlaceIndex_stageData
    (f : SourceFinitePlaceIndex I) (n : Int) (j : Nat) (v : V) :
    (stageDatumOfSourceFinitePlaceIndex I f n j).stageData v =
      sourceInd3StageData I n v :=
  rfl

/-- The stage poly-isomorphism of the datum is S1266's actual poly-isomorphism. -/
@[simp] theorem stageDatumOfSourceFinitePlaceIndex_stagePolyIso
    (f : SourceFinitePlaceIndex I) (n : Int) (j : Nat) (m : Int) :
    (stageDatumOfSourceFinitePlaceIndex I f n j).stagePolyIso m =
      ind3StagePolyIso I n m :=
  rfl

/-! ## 5. The actual-place comparison is the identity -/

/-- On the actual total place type the comparison is the identity map; this is
the canonical exact case already used by S1327's integralInd3LogShellCarrier.
It is recorded here to separate the canonical actual-place case from the
source-place gap. -/
def identityOnActualPlaces : IntegralPlaceTotal I → IntegralPlaceTotal I :=
  id

/-- The identity actual-place comparison has the exact actual integral shell
as its first field. -/
theorem identityOnActualPlaces_apply (x : IntegralPlaceTotal I) :
    identityOnActualPlaces I x = x :=
  rfl

/-- S1327's actual-place carrier has the exact actual integral shell. -/
theorem actualPlaceCarrier_shell (j : Nat) (i : Capsule j)
    (x : IntegralPlaceTotal I) :
    (integralInd3LogShellCarrier I j).shell i x =
      integralShell I x.1 x.2 :=
  rfl

/-! ## 6. Axiom probes -/

#print axioms comparisonOfFinitePlaceIndex
#print axioms sigma_mk_eq_self
#print axioms comparisonEquivSourceFinitePlaceIndex
#print axioms integralInd3PlaceComparisonRequired_iff_sourceFinitePlaceIndex
#print axioms carrierOfSourceFinitePlaceIndex
#print axioms carrierOfSourceFinitePlaceIndex_shell
#print axioms carrierOfSourceFinitePlaceIndex_shell_nontrivial
#print axioms carrierOfSourceFinitePlaceIndex_shell_not_rat_smul_closed
#print axioms stageDatumOfSourceFinitePlaceIndex
#print axioms identityOnActualPlaces

end LeanFormal.IUT.XiFPaper.S1427Ind3PlaceComparisonActual

namespace LeanFormal.IUT.Audit

/-- Status record for S1427. -/
def s1427Ind3PlaceComparisonActual : Obligation :=
  { id := "IUT-III.Ind3.integral-place-comparison-actual"
    source :=
      "IUT III, Theorem 3.11, (ii), (Ind3); IUT III, Definition 1.1, (i); " ++
        "IUT II, Definition 4.9, (i)"
    status := VerificationStatus.conditional
    note :=
      "The exact first field of the S1327 integral Ind3 carrier at the source " ++
        "place type V is the place comparison V -> (vQ, v).  Proved: it is " ++
        "canonically equivalent to a source finite-place index map " ++
        "V -> NumberField.FinitePlace Fmod (both round trips proved; the " ++
        "nontrivial one by Sigma.subtype_ext), and hence its requirement is " ++
        "equivalent to Nonempty of that source index.  For every supplied " ++
        "source finite-place index map, the actual carrier is constructed; " ++
        "its first field is definitionally the S1313 integral log-shell " ++
        "actualIntegralLogShell at the selected place, and the V-indexed " ++
        "Ind3 stage datum is filled with S1266's actual stage data.  The " ++
        "selected shells are proved nontrivial, not the whole local field, " ++
        "with full Q_p-span, and not closed under p^{-1} or rational scalars, " ++
        "so no IQSpan/Q-vector surrogate is used.  For a general OriginalInput " ++
        "no source finite-place index map is constructed: V is arbitrary and " ++
        "the source selected/bad place types are opaque, so the exact first " ++
        "missing datum is the source finite-place index itself.  No constant " ++
        "place map, Classical.choice place, Nonempty gate, IQSpan or Q-vector " ++
        "is asserted."
    dependsOn :=
      [ "IUT-III.Ind3.times-mu-stage-actual"
      , "IUT-III.integral-log-shell-contract-actual"
      , "IUT-III.Ind3.integral-log-shell-carrier-actual" ] }

end LeanFormal.IUT.Audit
