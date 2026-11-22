/-
  Reduction pass for constructing a source-facing Hodge-theater family
  from Definition 3.1 data.

  Paper anchor (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`; the PDF extraction writes ligatures such as
  "De nition", so the quotations below are normalized):

  * Definition 3.1 (extraction line 3123): "initial Theta-data" is a
    collection of data (F/F-bar, X_F, l, C_K, V, V_bad, ...); it carries
    the arithmetic input but no prime strip.
  * Theorem A preamble (line 736): "Fix a collection of initial
    Theta-data [cf. Definition 3.1], which determines, in particular,
    data (E_F, F, l, V) ... Then one may construct a Theta^{+-ell}NF-Hodge
    theater ... associated to this initial Theta-data".
  * Theorem A (iii) (line 822): "Let {nHT^{Theta+-ellNF}}_{n in Z} be a
    collection of distinct ... Hodge theaters [relative to the given
    initial Theta-data] indexed by the integers", linked into an infinite
    Theta-linked chain (the Frobenius-picture), which fails to have
    permutation automorphisms that switch adjacent indices.
  * Corollary 3.8 (line 5039): the same shape for the distinct
    Theta-Hodge theaters {nHT^Theta}_{n in Z}, chained by Corollary 3.7
    (i); Remark 3.8.1 (i) (line 5069): the Theta-link maps
    n Theta_v |-> (n+1) q_v.

  Frozen reduction target.  The family contract
  (`SourceHodgeTheaterFamily`) and its law groups are already proved;
  the open source obligation is the construction of a family from
  Definition 3.1 data.  Reduced here:

  (R1) Arbitrary index: from injective per-index arithmetic data with one
       shared prime strip and packet, the family exists and every
       contract law holds (fully proved; generalizes the Bool witness of
       the laws reduction to an arbitrary index type).
  (R2) Source-shaped assembly: from ONE arithmetic datum, one packet, an
       injective prime-strip family, and a coherent `FPrimeStripEquiv`
       system (identity, symmetry, composition), a family exists whose
       every member carries the source arithmetic datum (fully proved,
       conditional on the strip supply).  This is exactly the shape
       demanded by `Theorem311Source.OriginalInput` (`arithmetic_alignment`,
       `index_equiv`) and consumed by `SourceH1H2Construction` and
       `SourceHodgeTheaterBridge`.
  (R3) Necessity: under that alignment, distinctness forces pairwise
       distinct prime strips; if all prime strips coincide as well, the
       index is a subsingleton.  So the construction content of the
       source family is carried by the prime-strip supply: an injective
       prime-strip family with its coherent equivalence system (the
       source's Theta-link data, Corollary 3.7 (i)).  Definition 3.1 data
       itself has no prime strip
       (`SourceTheaterRealization.carrierNotDeterminedByRecord`).

  Not asserted (card `IUT-I.hodge-theater-family-source-reduction`): the
  supply of the injective prime-strip family and its coherent equivalence
  system for the source's {nHT}_{n in Z} over fixed initial Theta-data.
  The (R1) family varies arithmetic data and is not the consumer's
  aligned shape; the (R2) family is conditional on its strip supply.
  Neither is claimed to be the source's Z-chain; finite witnesses are not
  the general family.
-/

import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamilyLawsReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

set_option linter.checkUnivs false

namespace LeanFormal.IUT

open LeanFormal.IUT.InitialThetaSource

noncomputable section

universe ua uv upi umon ui

/-! ## 1. The same-strip link algebra at an arbitrary index type -/

theorem hodgeTheaterSameStripLink_refl {l : PrimeGeFive} {V : Type*}
    (A : InitialThetaArithmeticData l) (P : FPrimeStrip V)
    (θ : FiniteThetaPacket l) :
    hodgeTheaterSameStripLink A A P θ =
      HodgeTheaterLink.refl (⟨A, P, θ⟩ : HodgeTheater l V) :=
  rfl

theorem hodgeTheaterSameStripLink_symm {l : PrimeGeFive} {V : Type*}
    (A A' : InitialThetaArithmeticData l) (P : FPrimeStrip V)
    (θ : FiniteThetaPacket l) :
    HodgeTheaterLink.symm (hodgeTheaterSameStripLink A A' P θ) =
      hodgeTheaterSameStripLink A' A P θ :=
  rfl

theorem hodgeTheaterSameStripLink_trans {l : PrimeGeFive} {V : Type*}
    (A A' A'' : InitialThetaArithmeticData l) (P : FPrimeStrip V)
    (θ : FiniteThetaPacket l) :
    HodgeTheaterLink.trans (hodgeTheaterSameStripLink A A' P θ)
        (hodgeTheaterSameStripLink A' A'' P θ) =
      hodgeTheaterSameStripLink A A'' P θ :=
  rfl

theorem hodgeTheaterSameStripLink_naturality {l : PrimeGeFive}
    {V : Type*} {I : Type*} (A : I → InitialThetaArithmeticData l)
    (P : FPrimeStrip V) (θ : FiniteThetaPacket l) (i j : I) :
    HodgeTheaterLink.trans (hodgeTheaterSameStripLink (A i) (A j) P θ)
        (HodgeTheaterLink.refl ((⟨A j, P, θ⟩ : HodgeTheater l V))) =
      HodgeTheaterLink.trans
        (HodgeTheaterLink.refl ((⟨A i, P, θ⟩ : HodgeTheater l V)))
        (hodgeTheaterSameStripLink (A i) (A j) P θ) := by
  rw [HodgeTheaterLink.trans_refl, HodgeTheaterLink.refl_trans]

def distinctArithmeticSpineFamily {l : PrimeGeFive} {V : Type*}
    {I : Type*} (A : I → InitialThetaArithmeticData l)
    (hA : Function.Injective A) (P : FPrimeStrip V)
    (θ : FiniteThetaPacket l) :
    SourceHodgeTheaterFamily l V where
  index := I
  theater := fun i => ⟨A i, P, θ⟩
  distinct := by
    intro i j h
    exact hA (congrArg (fun T : HodgeTheater l V => T.arithmetic) h)
  link := fun i j => hodgeTheaterSameStripLink (A i) (A j) P θ
  link_refl := fun i => hodgeTheaterSameStripLink_refl (A i) P θ
  link_symm := fun i j => hodgeTheaterSameStripLink_symm (A i) (A j) P θ
  link_trans := fun i j k =>
    hodgeTheaterSameStripLink_trans (A i) (A j) (A k) P θ
  permutation := Equiv.refl I
  permutationLink := fun i =>
    HodgeTheaterLink.refl ((⟨A i, P, θ⟩ : HodgeTheater l V))
  permutation_naturality := fun i j =>
    hodgeTheaterSameStripLink_naturality A P θ i j

theorem distinctArithmeticSpineFamily_theater {l : PrimeGeFive}
    {V : Type*} {I : Type*} (A : I → InitialThetaArithmeticData l)
    (hA : Function.Injective A) (P : FPrimeStrip V)
    (θ : FiniteThetaPacket l) (i : I) :
    (distinctArithmeticSpineFamily A hA P θ).theater i =
      (⟨A i, P, θ⟩ : HodgeTheater l V) :=
  rfl

theorem distinctArithmeticSpineFamily_link {l : PrimeGeFive}
    {V : Type*} {I : Type*} (A : I → InitialThetaArithmeticData l)
    (hA : Function.Injective A) (P : FPrimeStrip V)
    (θ : FiniteThetaPacket l) (i j : I) :
    (distinctArithmeticSpineFamily A hA P θ).link i j =
      hodgeTheaterSameStripLink (A i) (A j) P θ :=
  rfl

/-! ## 2. Source-shaped assembly: one arithmetic datum, a strip system -/

/-- A coherent system of prime-strip equivalences on a family of prime
strips: pairwise equivalences satisfying the identity, symmetry, and
composition laws.  In the source this is the Theta-link system of
Corollary 3.7 (i) and Corollary 3.8; it is a supply here, not built
from Definition 3.1 data. -/
structure FPrimeStripLinkSystem {V : Type*} {I : Type*}
    (P : I → FPrimeStrip V) where
  equiv : ∀ i j, FPrimeStripEquiv (P i) (P j)
  equiv_refl : ∀ i, equiv i i = FPrimeStripEquiv.refl (P i)
  equiv_symm : ∀ i j, FPrimeStripEquiv.symm (equiv i j) = equiv j i
  equiv_trans : ∀ i j k,
    FPrimeStripEquiv.trans (equiv i j) (equiv j k) = equiv i k

abbrev stripSpineTheater {l : PrimeGeFive} {V : Type*} {I : Type*}
    (A : InitialThetaArithmeticData l) (θ : FiniteThetaPacket l)
    (P : I → FPrimeStrip V) (i : I) : HodgeTheater l V :=
  ⟨A, P i, θ⟩

def stripSpineLink {l : PrimeGeFive} {V : Type*} {I : Type*}
    (A : InitialThetaArithmeticData l) (θ : FiniteThetaPacket l)
    {P : I → FPrimeStrip V} (E : FPrimeStripLinkSystem P) (i j : I) :
    HodgeTheaterLink (stripSpineTheater A θ P i)
      (stripSpineTheater A θ P j) where
  primeStripEquiv := E.equiv i j
  theta_q_eq := rfl
  theta_scale_eq := fun _ => rfl

theorem stripSpineLink_refl {l : PrimeGeFive} {V : Type*} {I : Type*}
    (A : InitialThetaArithmeticData l) (θ : FiniteThetaPacket l)
    {P : I → FPrimeStrip V} (E : FPrimeStripLinkSystem P) (i : I) :
    stripSpineLink A θ E i i =
      HodgeTheaterLink.refl (stripSpineTheater A θ P i) := by
  unfold stripSpineLink
  rw [E.equiv_refl i]
  rfl

theorem stripSpineLink_symm {l : PrimeGeFive} {V : Type*} {I : Type*}
    (A : InitialThetaArithmeticData l) (θ : FiniteThetaPacket l)
    {P : I → FPrimeStrip V} (E : FPrimeStripLinkSystem P) (i j : I) :
    HodgeTheaterLink.symm (stripSpineLink A θ E i j) =
      stripSpineLink A θ E j i := by
  unfold stripSpineLink HodgeTheaterLink.symm
  rw [E.equiv_symm i j]

theorem stripSpineLink_trans {l : PrimeGeFive} {V : Type*} {I : Type*}
    (A : InitialThetaArithmeticData l) (θ : FiniteThetaPacket l)
    {P : I → FPrimeStrip V} (E : FPrimeStripLinkSystem P) (i j k : I) :
    HodgeTheaterLink.trans (stripSpineLink A θ E i j)
        (stripSpineLink A θ E j k) =
      stripSpineLink A θ E i k := by
  unfold stripSpineLink HodgeTheaterLink.trans
  rw [E.equiv_trans i j k]

theorem stripSpineLink_naturality {l : PrimeGeFive} {V : Type*}
    {I : Type*} (A : InitialThetaArithmeticData l)
    (θ : FiniteThetaPacket l) {P : I → FPrimeStrip V}
    (E : FPrimeStripLinkSystem P) (i j : I) :
    HodgeTheaterLink.trans (stripSpineLink A θ E i j)
        (HodgeTheaterLink.refl (stripSpineTheater A θ P j)) =
      HodgeTheaterLink.trans
        (HodgeTheaterLink.refl (stripSpineTheater A θ P i))
        (stripSpineLink A θ E i j) := by
  rw [HodgeTheaterLink.trans_refl, HodgeTheaterLink.refl_trans]

def stripSpineFamily {l : PrimeGeFive} {V : Type*} {I : Type*}
    (A : InitialThetaArithmeticData l) (θ : FiniteThetaPacket l)
    (P : I → FPrimeStrip V) (hP : Function.Injective P)
    (E : FPrimeStripLinkSystem P) :
    SourceHodgeTheaterFamily l V where
  index := I
  theater := stripSpineTheater A θ P
  distinct := by
    intro i j h
    exact hP (congrArg (fun T : HodgeTheater l V => T.primeStrip) h)
  link := stripSpineLink A θ E
  link_refl := fun i => stripSpineLink_refl A θ E i
  link_symm := fun i j => stripSpineLink_symm A θ E i j
  link_trans := fun i j k => stripSpineLink_trans A θ E i j k
  permutation := Equiv.refl I
  permutationLink := fun i =>
    HodgeTheaterLink.refl (stripSpineTheater A θ P i)
  permutation_naturality := fun i j =>
    stripSpineLink_naturality A θ E i j

theorem stripSpineFamily_theater {l : PrimeGeFive} {V : Type*}
    {I : Type*} (A : InitialThetaArithmeticData l)
    (θ : FiniteThetaPacket l) (P : I → FPrimeStrip V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) (i : I) :
    (stripSpineFamily A θ P hP E).theater i =
      stripSpineTheater A θ P i :=
  rfl

theorem stripSpineFamily_link {l : PrimeGeFive} {V : Type*}
    {I : Type*} (A : InitialThetaArithmeticData l)
    (θ : FiniteThetaPacket l) (P : I → FPrimeStrip V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) (i j : I) :
    (stripSpineFamily A θ P hP E).link i j =
      stripSpineLink A θ E i j :=
  rfl

theorem stripSpineFamily_arithmetic_alignment {l : PrimeGeFive}
    {V : Type*} {I : Type*} (A : InitialThetaArithmeticData l)
    (θ : FiniteThetaPacket l) (P : I → FPrimeStrip V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) (i : I) :
    ((stripSpineFamily A θ P hP E).theater i).arithmetic = A :=
  rfl

theorem stripSpineFamily_primeStrip {l : PrimeGeFive} {V : Type*}
    {I : Type*} (A : InitialThetaArithmeticData l)
    (θ : FiniteThetaPacket l) (P : I → FPrimeStrip V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) (i : I) :
    ((stripSpineFamily A θ P hP E).theater i).primeStrip = P i :=
  rfl

theorem stripSpineFamily_primeStrip_injective {l : PrimeGeFive}
    {V : Type*} {I : Type*} (A : InitialThetaArithmeticData l)
    (θ : FiniteThetaPacket l) (P : I → FPrimeStrip V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) :
    Function.Injective
      (fun i => ((stripSpineFamily A θ P hP E).theater i).primeStrip) := by
  intro i j h
  exact hP h

/-! ## 3. Necessity: with aligned arithmetic, distinctness lives in the
strips -/

theorem primeStrip_ne_of_index_ne_of_arithmetic_eq {l : PrimeGeFive}
    {V : Type*} (F : SourceHodgeTheaterFamily l V)
    {A : InitialThetaArithmeticData l}
    (hA : ∀ i, (F.theater i).arithmetic = A) {i j : F.index}
    (hij : i ≠ j) :
    (F.theater i).primeStrip ≠ (F.theater j).primeStrip := by
  intro hP
  exact hij (F.index_eq_of_arithmetic_primeStrip_eq i j
    ((hA i).trans (hA j).symm) hP)

theorem subsingleton_index_of_constant_primeStrips_of_arithmetic_eq
    {l : PrimeGeFive} {V : Type*} (F : SourceHodgeTheaterFamily l V)
    {A : InitialThetaArithmeticData l} {P : FPrimeStrip V}
    (hA : ∀ i, (F.theater i).arithmetic = A)
    (hP : ∀ i, (F.theater i).primeStrip = P) :
    Subsingleton F.index :=
  ⟨fun i j => F.index_eq_of_arithmetic_primeStrip_eq i j
    ((hA i).trans (hA j).symm) ((hP i).trans (hP j).symm)⟩

theorem exists_primeStrip_ne_of_index_ne {l : PrimeGeFive} {V : Type*}
    (F : SourceHodgeTheaterFamily l V) {A : InitialThetaArithmeticData l}
    (hA : ∀ i, (F.theater i).arithmetic = A) {i j : F.index}
    (hij : i ≠ j) :
    ∃ a b : F.index, (F.theater a).primeStrip ≠ (F.theater b).primeStrip :=
  ⟨i, j, primeStrip_ne_of_index_ne_of_arithmetic_eq F hA hij⟩

/-! ## 4. The Definition 3.1 root -/

def sourceInitialThetaArithmetic {l : PrimeGeFive}
    (S : SourceInitialThetaData l) : InitialThetaArithmeticData l :=
  S.candidate.arithmetic

theorem sourceInitialThetaArithmetic_spec {l : PrimeGeFive}
    (S : SourceInitialThetaData l) :
    sourceInitialThetaArithmetic S = S.candidate.arithmetic :=
  rfl

def sourceInitialThetaSpineFamily {l : PrimeGeFive}
    (S : SourceInitialThetaData l) {I : Type*}
    (θ : FiniteThetaPacket l) (P : I → FPrimeStrip S.candidate.V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) :
    SourceHodgeTheaterFamily l S.candidate.V :=
  stripSpineFamily (sourceInitialThetaArithmetic S) θ P hP E

theorem sourceInitialThetaSpineFamily_theater_arithmetic
    {l : PrimeGeFive} (S : SourceInitialThetaData l) {I : Type*}
    (θ : FiniteThetaPacket l) (P : I → FPrimeStrip S.candidate.V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) (i : I) :
    ((sourceInitialThetaSpineFamily S θ P hP E).theater i).arithmetic =
      S.candidate.arithmetic :=
  rfl

/-! ## 5. Source card: the strip supply for {nHT} indexed by Z -/

-- Card (not asserted here, consumers noted in the audit below): for fixed
-- Definition 3.1 data, the source family {nHT}_{n in Z} requires a supply
-- of an injective prime-strip family P : I -> FPrimeStrip V together with
-- a coherent FPrimeStripEquiv system (structure FPrimeStripLinkSystem).
-- Definition 3.1 data determines neither; the source supplies this via the
-- Theta-link machinery of Corollary 3.7 (i) / Corollary 3.8, whose
-- displacement structure is a separate obligation (C2b cards).

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def hodgeTheaterFamilySourceReduction : Obligation :=
  { id := "IUT-I.hodge-theater-family-source-reduction"
    source :=
      "IUT I: Definition 3.1; Theorem A (iii); Corollary 3.7 (i); " ++
        "Corollary 3.8; Remark 3.8.1 (i); IUT III Theorem 3.11 input"
    status := VerificationStatus.interface
    note :=
      "Reduction pass for constructing a source Hodge-theater family " ++
        "from Definition 3.1 data. Proved here: (1) the same-strip link " ++
        "algebra (identity, symmetry, composition, naturality) at an " ++
        "arbitrary index type, and a family over any index from " ++
        "injective per-index arithmetic data with one shared prime strip " ++
        "and packet, generalizing the Bool witness; (2) a conditional " ++
        "source-shaped assembly: from one arithmetic datum, one packet, " ++
        "an injective prime-strip family, and a coherent FPrimeStripEquiv " ++
        "system (identity/symmetry/composition laws), a family exists in " ++
        "which every member carries the source arithmetic datum, with all " ++
        "contract laws proved; (3) necessity: in that aligned shape, " ++
        "distinctness forces pairwise distinct prime strips, and constant " ++
        "aligned data yields a subsingleton index. Not constructed " ++
        "(card): the supply of the injective prime-strip family and its " ++
        "coherent equivalence system for the source's {nHT} indexed by Z " ++
        "over fixed initial Theta-data; the Theta-link data of Corollary " ++
        "3.7 (i) is exactly this supply (cf. Remark 3.8.1 (i)), and " ++
        "Definition 3.1 data carries no prime strip " ++
        "(IUT-I.source-theater-carrier-nondetermination). Consumers: " ++
        "Theorem311Source.OriginalInput (arithmetic_alignment, " ++
        "index_equiv), SourceH1H2Construction, SourceHodgeTheaterBridge."
    dependsOn :=
      [ "IUT-I.hodge-theater-family-source-laws",
        "IUT-I.hodge-theater-family-laws-reduction",
        "IUT-I.hodge-theater-carrier-and-links",
        "IUT-I-II.prime-strip-core",
        "IUT-I.source-theater-carrier-nondetermination" ] }

end LeanFormal.IUT.Audit
