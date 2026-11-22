# C9 IUT bridge obligations: Theorem311, SourceP1P2Bundle, SourceTheorem311ReferenceOutput

Task: task-474. Owner: kummer. Date: 2026-10-25.
Audit of actual project declarations only; no Lean edits; no toy fields;
no mixed/E3. Only this file written. target_accepted=false; P6 open.

## 0. Audited declarations

- LeanFormal/IUT/IUTIII/Theorem311/Obligations.lean, 13 lines,
  SHA256 40cd308a94bea76c7b1160af6d01c46790216d647dbff2fd0024bddf3a1000e3.
- LeanFormal/IUT/IUTIII/Theorem311/SourceInternalWiring.lean, 1771 lines,
  SHA256 da6a52b798ef69050d4ab389bcb3c04af4aa881507a1befcd7e32afc8c03c3bc.
- LeanFormal/IUT/IUTIII/Theorem311/SourceTheorem311ReferenceContract.lean,
  534 lines,
  SHA256 c8e27459ebcc988173c59c9b17e4a23e7998e235a3443c6c836410a63381cc21.
- LeanFormal/IUT/IUTIII/Theorem311/SourceTheorem311Assembly.lean, 1478 lines,
  SHA256 49998eda25022bcde0b25f5732b719b20084fecc06eaa57cf944f2db2bb5ee04.

No actual sorry or axiom occurs in these four files (grep for sorry/axiom returns
zero source occurrences). The only status markers are the Obligation records
and the structure boundary fields described below.

## 1. Obligations.lean: actual pending obligation

The file contains one actual Obligation record:

    theorem311Output : Obligation
      id = "IUT-III.theorem-3.11-output"
      source = "IUT III, Theorem 3.11"
      status = VerificationStatus.pending
      note = "Construct the multiradial output over the actual IUT I-II data."
      dependsOn = ["IUT-I.initial-theta-data",
                   "IUT-I-II.prime-strips-frobenioids",
                   "IUT-II.vertical-log-kummer"]

This is the actual pending theorem-level obligation. It is not a proof term,
not a sorry, and not an axiom; it is a status record. No theorem constructing
the multiradial output over OriginalInput exists in this file.

## 2. SourceP1P2Bundle: actual fields and premises

SourceInternalWiring.lean defines:

### 2.1 SourceP1P2Input (lines 1393-1407)

    structure SourceP1P2Input (W : SourceInternalWiring I R P X Y) where
      lgp : SourceP1.LGPBoundary R V
      volume : SourceP1.VolumeBoundary R
      kummer : SourceP2.KummerBoundary R
      permutation : SourceP2.PermutationBoundary R

These are actual boundary records for LGP, volume, Kummer and permutation
data. They are premises, not constructed in this file from OriginalInput.

### 2.2 SourceP1P2Bundle (lines 1441-1486)

    structure SourceP1P2Bundle
      (W : SourceInternalWiring I R P X Y)
      (S : SourceP1P2Input W) where
      theorem15 : SourceTheorem15Coricity R.procession
      proposition21 : SourceProposition21Kummer Choice Choice
      proposition23 : SourceCorollary23Permutation Choice Choice
      proposition32 : SourceProposition32Packet R.procession R.packet
      proposition34 : SourceProposition34LGP Label Choice V
      proposition35 : SourceProposition35Vertical R.procession R.packet R.vertical
      proposition37Local : SourceProposition37Frobenioid X
      proposition37Global : SourceProposition37Frobenioid Y
      proposition39 : SourceProposition39Volume Choice
      proposition310 : SourceProposition310Comparison Choice Choice
      dependency : SourceTheorem311DependencyPackage R
      theorem15_eq : ...
      proposition21_eq : ...
      proposition23_eq : ...
      proposition32_eq : ...
      proposition34_eq : ...
      proposition35_eq : ...
      proposition37Local_eq : ...
      proposition37Global_eq : ...
      proposition39_eq : ...
      proposition310_eq : ...
      dependency_*_eq : ...

The equality fields are part of the record, not axioms; they are supplied by
the constructors below.

### 2.3 Constructors

    SourceP1P2Bundle.assemble (W : SourceInternalWiring) (S : SourceP1P2Input W)
      : SourceP1P2Bundle W S

    SourceP1P2Bundle.canonical
      (A : SourceH1H2Alignment I R)
      (P : H2SpokePermutation I)
      (B : K2FrobenioidBoundary R (k1OfRealization R) X Y)
      (S : SourceP1P2Input (W := SourceInternalWiring.canonical A P B))
      : SourceP1P2Bundle (SourceInternalWiring.canonical A P B) S

Therefore a bundle is constructed only after supplying the actual explicit
premises:

- SourceInternalWiring W (H1/H2 alignment layer), or
- SourceH1H2Alignment A + H2SpokePermutation P + K2FrobenioidBoundary B, and
- SourceP1P2Input S (LGP, volume, Kummer, permutation boundaries).

No constructor of SourceP1P2Input from OriginalInput occurs in the audited
files. No constructor of SourceInternalWiring from OriginalInput alone occurs
here; canonical takes A/P/B. No term of SourceP1P2Bundle exists without these
premises.

## 3. SourceTheorem311ReferenceOutput: contract, not existence

SourceTheorem311ReferenceContract.lean defines:

    structure SourceTheorem311ReferenceOutput
      (B : SourceP1P2Bundle W S) where
      output : Theorem311Output R.input
      partI : PartI R.input
      partII : PartII R.input
      partIII : PartIII R.input
      output_partI : output.part_i = partI
      output_partII : output.part_ii = partII
      output_partIII : output.part_iii = partIII
      output_eq : output = B.dependency.output
      h1_source : W.h1.source = I.initial
      h2_h1 : W.h2.h1 = W.h1
      h2_procession_toD : W.h2.fProcession.toD = W.h2.dProcession
      h2_permutation : W.h2.permutation = P
      stage_cardinality : ...
      stage_inclusion_injective : ...
      t1 : ... t2 : ... t3 : ...
      final output/indeterminacy fields: output_source, output_quotient,
      output_labelled, output_ind1, output_ind2, output_ind3,
      output_horizontal, output_evaluation.

Constructors:

    SourceTheorem311ReferenceOutput.assemble (B : SourceP1P2Bundle W S)
      : SourceTheorem311ReferenceOutput B

    canonicalReferenceOutput
      (A : SourceH1H2Alignment I R)
      (P : H2SpokePermutation I)
      (K : K2FrobenioidBoundary R (k1OfRealization R) X Y)
      (S : SourceP1P2Input (W := SourceInternalWiring.canonical A P K))
      : SourceTheorem311ReferenceOutput
          (SourceP1P2Bundle.canonical A P K S)

The file's own header says this is a consumer-facing contract, not an
existence shortcut; the final audit obligation is:

    theorem311ReferenceOutputContract : Obligation
      status = VerificationStatus.interface
      note = "constructed from SourceP1P2Bundle, so it closes the output arrow
              contract but does not claim arithmetic-to-source existence."
      dependsOn = ["IUT-III.theorem-3.11-internal-wiring",
                   "IUT-III.theorem-3.11-conditional-T1-T3-assembly"]

Thus the reference output is constructed only from a supplied bundle B; it is
not constructed from OriginalInput.

## 4. What is pending

Pending theorem/proof:

1. Construct the actual multiradial output over the actual IUT I-II data:
   Obligations.theorem311Output, status pending.
2. Construct SourceP1P2Bundle from actual source data, i.e. supply
   SourceInternalWiring W + SourceP1P2Input S (or A/P/B/S for canonical).
   The audited files provide no such constructor from OriginalInput alone.
3. Supply the source boundary records:
   - SourceP1.LGPBoundary,
   - SourceP1.VolumeBoundary,
   - SourceP2.KummerBoundary,
   - SourceP2.PermutationBoundary,
   - SourceH1H2Alignment,
   - H2SpokePermutation,
   - K2FrobenioidBoundary.
4. From those, the ReferenceOutput contract follows by assemble/canonical,
   not independently.

Not pending in the sense of missing code: the typed assembly/equality fields
are actually implemented by assemble/canonical; there is no sorry/axiom in the
audited files. But they are conditional on the explicit boundary premises.

## 5. What would construct the bundle

The exact constructive routes are:

(A) SourceP1P2Bundle.assemble W S:
    supply W : SourceInternalWiring and S : SourceP1P2Input W.

(B) SourceP1P2Bundle.canonical A P K S:
    supply H1H2Alignment A, H2SpokePermutation P, K2FrobenioidBoundary K,
    and S over W = SourceInternalWiring.canonical A P K.

For the reference contract, append:

(C) SourceTheorem311ReferenceOutput.assemble B for a bundle B, or
    canonicalReferenceOutput A P K S.

No other constructor is present in the audited declarations. Thus the actual
missing bridge is the construction of S (and W/A/P/K) from OriginalInput; the
bundle/reference contract machinery is already implemented conditionally.

## 6. Exact status classification

| declaration | status |
|---|---|
| Obligations.theorem311Output | actual pending obligation, no proof term |
| SourceP1P2Input | actual boundary structure, not constructed |
| SourceP1P2Bundle | actual structure, conditional on W,S |
| SourceP1P2Bundle.assemble | actual constructor from W,S |
| SourceP1P2Bundle.canonical | actual constructor from A,P,K,S |
| SourceTheorem311ReferenceOutput | actual contract structure |
| ReferenceOutput.assemble | actual constructor from bundle |
| canonicalReferenceOutput | actual constructor from A,P,K,S |
| constructor from OriginalInput alone | absent |
| sorry/axiom in audited files | none |
| multiradial output over actual IUT I-II | pending |

## 7. Conclusion

The audited declarations show a clean conditional bridge, not an unconditional
construction. Theorem311/Obligations.lean records the actual pending output
obligation; SourceP1P2Bundle is a record of source boundary data plus theorem
fields, constructed by assemble or canonical; SourceTheorem311ReferenceOutput is
a consumer contract whose fields are assembled from a supplied bundle. No
constructor from OriginalInput alone exists in these files, and no sorry/axiom
is used. The missing step is exactly the construction of the bundle's explicit
source premises (LGP, volume, Kummer, permutation, H1/H2 alignment, K2
Frobenioid boundary) from the actual IUT I-II data. Until that is supplied, the
reference output contract is conditional.

No Lean edits; no toy fields; no mixed/E3; target_accepted=false; P6 open.

## 8. Status

- Audit only; no Lean/Project edits.
- Pending theorem311Output and bundle-client premises identified; constructors
  and exact boundary records listed.
- target_accepted=false.
