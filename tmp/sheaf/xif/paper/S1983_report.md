# S1983: [EtTh] type-name -> OrbicurveSignature bridge (actual)

Date: 2026-11-01 (Asia/Shanghai)
Workspace: D:\lean
Scope: [EtTh] Section 0 / Definition 2.1 / Definition 2.3; IUT I Definition 3.1;
       the C_F / C_K / C_K^-> honest signatures; the Lean labels in
       SourceDefinition31Quantifiers.lean.
Status: EXIT=0. Bridge constructed (definition + theorem, no axiom, no sorry).
        No production definition changed. Only new bridge/audit files.

## Result

* File: tmp/sheaf/xif/paper/S1983EtThSignatureBridgeActual.lean
  - 40551 bytes
  - SHA256 7E361BCA34992387407A4D24A6D0674C15FB640EC68BBC1B2F07F5FD7EEF3043
  - 96 declarations (76 theorems, 14 defs, 4 abbrevs, 1 structure, 1 inductive),
    0 errors, 0 warnings, no sorry/admit/axiom
* OLean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1983EtThSignatureBridgeActual.olean
  - 598680 bytes
  - SHA256 F4EE16CE84E234AEA9E7DB2A352494F3780CDC652874B5BFDA72152B967F9152
* Compile: lake env lean -j1 -o <olean> <file>  =>  EXIT = 0
  log: tmp/sheaf/xif/paper/S1983_compile.log (3930 bytes, 0 error/warning,
       26 #print axioms blocks, only propext / Classical.choice / Quot.sound,
       0 sorryAx)
* OLean import check: tmp/sheaf/xif/paper/_S1983OleanCheck.lean
  log: tmp/sheaf/xif/paper/S1983_olean_check.log (CHECK_EXIT = 0)

## The bridge

Definition EtThType: the four [EtTh] type names
    oneOne (1,1) | oneOnePlusMinus (1,1)^± | oneLTors l (1,l-tors) | oneLTorsPlusMinus l (1,l-tors)^±
with EtThType.prequotient (signature of the curve quotiented by ±1) and
EtThType.isSignQuotient.

Definition SignQuotientInput / SignQuotientInput.quotient: the ±1 stack quotient
at signature level, from the geometric input
    (genus 1, no stacky points, odd number n of cusps with exactly one fixed cusp)
producing (0; [2,2,2]; (n+1)/2).  The quotient is *forced*, not chosen:
    SignQuotientInput.quotient_unique :
      genus T = 0 -> stackyOrders T = [2,2,2] ->
      2 * chi T = chi source -> T = quotient.
Euler relation: SignQuotientInput.quotient_eulerCharacteristic :
    2 * chi(quotient) = chi(source).

Definition etthSignature : EtThType -> Iut.OrbicurveSignature
    (1,1)        |-> (1; []; 1)            = oncePuncturedElliptic
    (1,1)^±      |-> (0; [2,2,2]; 1)       = S1964HonestQuotientSignature (paperCF)
    (1,l-tors)   |-> (1; []; l)            = honestXKTors l
    (1,l-tors)^± |-> (0; [2,2,2]; (l+1)/2) = honestCKTors l

Bridge theorems (all machine checked):
* etthSignature_oneOnePlusMinus_eq_honestSignature :
      etthSignature (1,1)^± = S1964HonestQuotientSignature
* etthSignature_oneOnePlusMinus_eq_paperCF : ... = paperCF
* etthSignature_oneOne_eq_legacyTypeOneOne :
      etthSignature (1,1) = toIutSignature SourceOrbicurveSignature.typeOneOne
* etthSignature_oneLTors_eq_honestXKTors, etthSignature_oneLTorsPlusMinus_eq_honestCKTors
* etthSignature_oneOnePlusMinus_euler : chi((1,1)^±) = -1/2
* etthSignature_oneOnePlusMinus_euler_two_mul : 2 chi((1,1)^±) = chi((1,1)) = -1
* etthSignature_oneLTors_euler : chi(1,l-tors) = -l
* etthSignature_oneLTorsPlusMinus_euler : chi((1,l-tors)^±) = -l/2
* etthSignature_oneLTors_euler_l : chi(1,l-tors) = l * chi((1,1))
* etthSignature_oneLTorsPlusMinus_euler_l : chi((1,l-tors)^±) = l * chi((1,1)^±)
* etthSignature_oneLTors_euler_two_mul : 2 chi((1,l-tors)^±) = chi(1,l-tors)
* etthSignature_isHyperbolic : all four types are hyperbolic

The paper's objects typed by [EtTh]:
* paperCFType = (1,1)^±, paperCKType = (1,1)^± (the K-core C_K := C_F x_F K is a
  base change, so it keeps the type and the signature (0;[2,2,2];1)),
  paperXFType = (1,1), paperCKTorsType l = (1,l-tors)^±.
* paperCF_signature, paperCK_signature, paperXF_signature, paperCKTors_signature.

Label verdicts (machine checked against the tree's labels):
* etthSignature_oneOnePlusMinus_ne_sourceTypeOneOnePlusMinus
      (1;[2];0) is a transcription error (genus 1 vs 0; [2] vs [2,2,2]; 0 vs 1 cusp)
* etthSignature_oneOnePlusMinus_euler_eq_paperLabel
      both chi = -1/2, so chi / hyperbolicity tests cannot detect the error
* etthSignature_oneOnePlusMinus_ne_legacyTypeOneOne
      the D-clause C_F label (1;[];1) is the X_F signature, not the quotient's
* etthSignature_oneLTors_ne_legacyTypeOneLTorsion
      (1;[l];0) is not (1;[];l)
* etthSignature_oneLTorsPlusMinus_ne_legacyTypeOneLTorsionPlusMinus
      (1;[2,l];0) is not (0;[2,2,2];(l+1)/2)
* etthSignature_oneLTorsPlusMinus_ne_oneOnePlusMinus
      the K-core (1,1)^± and the degree-l cover (1,l-tors)^± are different objects
* etthSignature_oneOnePlusMinus_ne_coarse
      the coarse quotient (0;[];1) has chi = 1 and is not hyperbolic
* sourceSignQuotientData_cF_ne_etth / _cK_ne_etth / _xF_eq_etth
      production contract: cF and cK metadata cannot be the honest [EtTh] signature;
      xF is correctly typed.

## The exact first missing (recorded, not postulated)

G1. The quotient stack [X_F/{±1}]: S1964FirstMissing l A (S1964) =
    Nonempty (S1964QuotientStructure l A).  Its four missing fields are the
    pointwise lax colimit of the sign action on the Cat-valued etale stack, its
    functoriality/coherence, Pseudofunctor.IsStack (stackification), and the
    bicategorical universal property (descend / factor / descendTwoCell /
    twoCellExt).  Machine-checked reduction:
      S1983EtThCF is S1964CFQuotientAt l A (etthSignature (1,1)^±) _,
      S1983EtThCF_iff_honest : Nonempty (S1983EtThCF l A) <-> Nonempty (S1964HonestCFQuotient l A),
      S1964FirstMissing_ofS1983 : S1983FirstMissing l A -> S1964FirstMissing l A.

G2. The signature-computation gap: S1983SignatureNotForcedByFiber: for EVERY
    etale stack fiber (with IsStack) there is a HyperbolicOrbicurve with that
    fiber and with signature the transcription label (1;[2];0) instead of the
    honest one.  Hence "the constructed quotient has signature (0;[2,2,2];1)" is
    not derivable from the fiber; the honest signature must be target data (as in
    S1983EtThCF) or the production signature field must be computed from geometry
    (a production-definition change, out of scope).

G3. The genus-0 component as pure geometry: S1983CoarseQuotientIsAffineLine,
    i.e. the fixed subring of S1726CoordinateRing under S1898CoordEndo is exactly
    the image of K[X] -> R', x |-> class of X_0.  The inclusion is proved
    (S1983PolyToCoordinateRing_mem, S1983PolyToCoordinateRing_comp); the reverse
    inclusion needs the normal form R' = K[x] (+) K[x]*y with
    y^2 = x^3 + (61/64)x^2 - (125/64)x, absent from the tree.
    With genus 0, the three order-two points and 2*chi = chi(X_F), the single cusp
    is forced: S1983_punctures_forced.

Grounding in the actual S1726 model (S1964 reused):
* S1983_fixedPoint_cases : the fixed points of the actual involution are exactly
  (0,0), (1,0), (-125/64,0) (both directions; S1964 had only the forward one).
* S1983FixedLocus_eq, S1983_fixedPoints_pairwise_distinct.
* S1983_stackyOrders_eq_fixedLocus : stackyOrders = [2,2,2] and the fixed locus
  is exactly those three points.

## Not done / not claimed

* No axiom, no sorry, no postulated quotient, no arbitrary carrier.
* No production definition changed (sourceTypeOneOnePlusMinus is untouched; the
  label mismatch is proved, not hidden).
* The K-core signature (0;[2,2,2];1) is recorded as paper data (base change
  preserves the [EtTh] type); the production contract only records genus
  preservation, which is exactly the audit's object-misplacement finding.
* Compiled against the artifact versions present at 18:52 (all imported oleans
  newer than their sources): S1972 audit olean 18:35:28, S1964 olean 18:06:20,
  S1726 olean 10-31 17:38:13, SourceDefinition31Quantifiers olean 11-01 02:34:59.

## Files added by this task

* tmp/sheaf/xif/paper/S1983EtThSignatureBridgeActual.lean
* tmp/sheaf/xif/paper/S1983EtThSignatureBridgeActual.olean (build artifact)
* tmp/sheaf/xif/paper/_S1983OleanCheck.lean
* tmp/sheaf/xif/paper/S1983_compile.log
* tmp/sheaf/xif/paper/S1983_olean_check.log
* tmp/sheaf/xif/paper/S1983_report.md (this file)


## Update 2026-11-01: G3 closed by S1990

S1990GenusZeroFixedSubringActual.lean proves the normal form R' = K[x] (+) K[x]*y and S1990CoarseQuotientIsAffineLine / S1983CoarseQuotientIsAffineLine_holds. The G3 paragraph above is superseded. G1 and G2 remain as stated.
