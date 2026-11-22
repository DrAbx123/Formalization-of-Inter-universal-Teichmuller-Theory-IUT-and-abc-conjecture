
end Realified

open Realified
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open IsDedekindDomain NumberField

/-! ## 1. The base field and the global realified Frobenioid C-mod -/

/-- The arithmetic base field Fmod of the S1895 paper input. -/
abbrev PaperFmod (D : S1895PaperInput) : Type :=
  (S1895PaperInput.I D).initial.arithmetic.Fmod

/-- The actual global realified Frobenioid C-mod of S1895PaperO: the
realification of the arithmetic Frobenioid of [FrdI], Example 6.3, over the
actual base field Fmod, built as a model Frobenioid presentation on the
realified effective arithmetic divisor monoid. -/
noncomputable def paperGlobalRealifiedFrobenioid
    (D : S1895PaperInput) : Iut.FrobenioidPresentation :=
  numberFieldFrobenioidPresentationRealified (F := PaperFmod D)

/-- The base object of the presentation is the unique object of the one-object
base category. -/
abbrev paperGlobalBaseObject (D : S1895PaperInput) :
    LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend.BottomBase :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend.bottomPoint

/-- The divisor monoid of C-mod at its unique base object is the actual
realified effective divisor monoid of Fmod. -/
theorem paperGlobalRealifiedFrobenioid_divisorMonoid
    (D : S1895PaperInput) :
    ((paperGlobalRealifiedFrobenioid D).preFrobenioid.divisorMonoid.obj
      (paperGlobalBaseObject D)).carrier =
      RealEffectiveDivisor (F := PaperFmod D) := rfl

/-- The Grothendieck group of the realified divisor monoid is the explicit real
arithmetic divisor group of Fmod. -/
theorem paperGlobalRealifiedFrobenioid_groupCompletion
    (D : S1895PaperInput) :
    Nonempty (AddEquiv
      (Algebra.GrothendieckAddGroup (RealEffectiveDivisor (F := PaperFmod D)))
      (RealExplicitDivisor (F := PaperFmod D))) :=
  ⟨realConeGrothendieckEquiv (F := PaperFmod D)⟩

/-! ## 2. The q_v zero-locus divisor -/

/-- The base Fmod prime of a bad place of the S1895 input. -/
noncomputable def paperBadBasePlace (D : S1895PaperInput)
    (b : (S1895PaperInput.I D).initial.badPlaces) :
    HeightOneSpectrum (NumberField.RingOfIntegers (PaperFmod D)) :=
  b.1.maximalIdeal

/-- The q_v zero-locus prime divisor at a bad base place, as an actual element
of the realified effective divisor monoid.  The coefficient is one: this is the
prime divisor underlying the zero locus.  The q_v order is the actual S1487
candidate order and is not replaced by a fake coefficient. -/
noncomputable def paperQVZeroLocusPrime (D : S1895PaperInput)
    (b : (S1895PaperInput.I D).initial.badPlaces) :
    RealEffectiveDivisor (F := PaperFmod D) :=
  (Finsupp.single (paperBadBasePlace D b) (1 : NNReal), fun _ => 0)

/-- The global q_v zero-locus divisor: the finite sum of the actual prime
divisors at all bad base places. -/
noncomputable def paperQVZeroLocusGlobal (D : S1895PaperInput) :
    RealEffectiveDivisor (F := PaperFmod D) :=
  letI := (S1895PaperInput.I D).initial.bad_finite
  sum (fun b : (S1895PaperInput.I D).initial.badPlaces => paperQVZeroLocusPrime D b)

/-- The global zero-locus divisor is exactly the finite sum of the local prime
divisors. -/
theorem paperQVZeroLocusGlobal_eq_sum (D : S1895PaperInput) :
    paperQVZeroLocusGlobal D =
      (letI := (S1895PaperInput.I D).initial.bad_finite
       sum (fun b : (S1895PaperInput.I D).initial.badPlaces =>
        paperQVZeroLocusPrime D b)) := rfl

/-- Each local q_v zero-locus divisor has the actual bad base prime in its
finite support. -/
theorem paperQVZeroLocusPrime_support (D : S1895PaperInput)
    (b : (S1895PaperInput.I D).initial.badPlaces) :
    (paperQVZeroLocusPrime D b).1 (paperBadBasePlace D b) = 1 := by
  simp [paperQVZeroLocusPrime]

/-! ## 3. The finite global log-shell/tensor packet -/

/-- The actual local log-shell datum at a finite prime place of the S1895
one-column.  The log-coordinate field is Real; the units are the units of the
actual completed local field; the invariant submonoid is the full unit group
(the Galois action is not modeled, exactly as in the reduced carrier); the log
map is the actual norm-log degree. -/
noncomputable def paperLogShellDatum (v : FinitePrimePlace 2 7) :
    SourceLogShellDatum where
  p := v.1
  hp := v.2.2.2
  K := Real
  Units := (actualLocalField v)ˣ
  invariants := top
  logMap := unitNormLogDegree (actualLocalField v)

/-- The actual finite global log-shell family over the one-column index V. -/
noncomputable def paperGlobalLogShellFamily :
    FinitePrimePlace 2 7 -> SourceLogShellDatum :=
  paperLogShellDatum

/-- The finite global log-shell direct-sum packet IQ(sum_v I_v). -/
noncomputable def paperGlobalLogShellPacket :
    Submodule Rat (FinitePrimePlace 2 7 -> Real) :=
  sourceLogShellIQDirectSumPacket paperGlobalLogShellFamily

/-- The packet is exactly the Q-span of the product of the actual local
log-shells. -/
theorem paperGlobalLogShellPacket_eq_span :
    paperGlobalLogShellPacket =
      Submodule.span Rat
        (sourceLogShellDirectSumPacketSet paperGlobalLogShellFamily) :=
  sourceLogShellIQDirectSumPacket_eq_span_pi paperGlobalLogShellFamily

/-- The reduced n-tensor log-shell packet over a finite factor set. -/
noncomputable def paperGlobalLogShellTensorPacket
    {A : Type} [Fintype A] (t : A -> Set Real) : Set Real :=
  sourceLogShellTensorProductSet t

/-- The tensor-packet Q-span decomposition. -/
theorem paperGlobalLogShellTensorPacket_span_eq
    {A : Type} [Fintype A] [DecidableEq A] (t : A -> Set Real) :
    Submodule.span Rat (paperGlobalLogShellTensorPacket t) =
      Submodule.span Rat
        (paperGlobalLogShellTensorPacket
          (fun a => (Submodule.span Rat (t a) : Set Real))) :=
  sourceLogShellTensorProductSet_span_eq t

/-! ## 4. The exact first missing: the archimedean log-shell -/

/-- The archimedean log-shell datum of IUT III, Definition 1.1, (ii): a compact
convex closed interval/orbit in the log-coordinate field, contained in the
closed unit ball.  This is a different carrier from SourceLogShellDatum, which
is nonarchimedean (it carries a prime p and a (p*_v)^{-1}-scaled
pre-log-shell). -/
structure ArchimedeanLogShellDatum where
  /-- the log-coordinate field at the archimedean place -/
  K : Type
  [fieldK : Field K]
  [charZeroK : CharZero K]
  [moduleK : Module Real K]
  [topologicalSpaceK : TopologicalSpace K]
  /-- the closed unit ball of the log-coordinate field -/
  unitBall : Set K
  /-- the archimedean log-shell (closed line segment / orbit) -/
  logShell : Set K
  /-- the log-shell is contained in the closed unit ball -/
  logShell_subset_unitBall : logShell ⊆ unitBall
  /-- the log-shell is convex over Real (the closed-interval shape) -/
  convex_logShell : Convex Real logShell
  /-- the log-shell is compact -/
  isCompact_logShell : IsCompact logShell

attribute [instance] ArchimedeanLogShellDatum.fieldK
  ArchimedeanLogShellDatum.charZeroK ArchimedeanLogShellDatum.moduleK
  ArchimedeanLogShellDatum.topologicalSpaceK

/-- The exact first missing object after the realified C-mod, the q_v
zero-locus divisor and the finite log-shell packet: an archimedean log-shell
datum at every archimedean place of Fmod.  No inhabitant is asserted. -/
def S1927FirstMissing (D : S1895PaperInput) : Type 1 :=
  (w : NumberField.InfinitePlace (PaperFmod D)) -> ArchimedeanLogShellDatum

/-- A SourceLogShellDatum is nonarchimedean: it carries a prime p.  This is
the structural reason the existing reduced log-shell carrier cannot supply the
archimedean first missing above. -/
theorem sourceLogShellDatum_carries_prime (L : SourceLogShellDatum) :
    Exists (fun p : Nat => Nat.Prime p) := ⟨L.p, L.hp⟩

/-! ## 5. The full log-Kummer on 1,circ U_Q and its exact missing inputs -/

/-- The actual Kummer evaluation square of IUT III, Theorem 3.11, (iii), (a),
(b), on four source F-prime-strips.  The paper's four coric vertices
env/gau/LGP/lgp are not constructed in the tree (SourceKummerEvaluationArrows
R3); the type is therefore parameterized by its four strips and does not
pretend that they are the paper vertices.  No inhabitant is asserted. -/
structure S1927KummerEvaluationSquareActual (D : S1895PaperInput) where
  upperLeft : FPrimeStrip (FinitePrimePlace 2 7)
  upperRight : FPrimeStrip (FinitePrimePlace 2 7)
  lowerLeft : FPrimeStrip (FinitePrimePlace 2 7)
  lowerRight : FPrimeStrip (FinitePrimePlace 2 7)
  square : SourceKummerEvaluationSquare
    (S1895KummerGroup (S1895PaperInput.I D))
    upperLeft upperRight lowerLeft lowerRight

/-- The full log-Kummer package on 1,circ U_Q.  The one-column structure and
its (1,0) label are the actual S1895PaperO data; the finite log-shell packet is
the constructed one; the archimedean log-shell and the Kummer evaluation
square are the two named missing inputs. -/
structure S1927FullLogKummerUQ (D : S1895PaperInput) where
  oneColumn : SourceOneColumnArithmeticHolomorphicStructure
    (FinitePrimePlace 2 7)
  oneColumn_eq : oneColumn = (S1895PaperO D).oneColumn
  label : S1895OneColumnLabel (FinitePrimePlace 2 7)
  label_eq : label = s1895PaperO_oneColumnLabel D
  finiteLogShell : Submodule Rat (FinitePrimePlace 2 7 -> Real)
  finiteLogShell_eq : finiteLogShell = paperGlobalLogShellPacket
  archimedeanLogShell : S1927FirstMissing D
  evaluationSquare : S1927KummerEvaluationSquareActual D

/-- Assembly of the full log-Kummer package from the constructed finite data
and the two named missing inputs. -/
noncomputable def s1927FullLogKummerUQ_of_missing
    (D : S1895PaperInput) (h : S1927FirstMissing D)
    (sq : S1927KummerEvaluationSquareActual D) :
    S1927FullLogKummerUQ D where
  oneColumn := (S1895PaperO D).oneColumn
  oneColumn_eq := rfl
  label := s1895PaperO_oneColumnLabel D
  label_eq := rfl
  finiteLogShell := paperGlobalLogShellPacket
  finiteLogShell_eq := rfl
  archimedeanLogShell := h
  evaluationSquare := sq

/-! ## 6. The constructed global package -/

/-- The three global objects constructed in this file, tied to the S1895 paper
input. -/
structure S1927ConstructedGlobalObjects (D : S1895PaperInput) where
  frobenioid : Iut.FrobenioidPresentation
  frobenioid_eq : frobenioid = paperGlobalRealifiedFrobenioid D
  qVZeroLocus : RealEffectiveDivisor (F := PaperFmod D)
  qVZeroLocus_eq : qVZeroLocus = paperQVZeroLocusGlobal D
  logShellPacket : Submodule Rat (FinitePrimePlace 2 7 -> Real)
  logShellPacket_eq : logShellPacket = paperGlobalLogShellPacket

/-- The global objects are constructed from the actual S1895 input, not from a
gate or an arbitrary inhabitant. -/
noncomputable def s1927ConstructedGlobalObjects (D : S1895PaperInput) :
    S1927ConstructedGlobalObjects D where
  frobenioid := paperGlobalRealifiedFrobenioid D
  frobenioid_eq := rfl
  qVZeroLocus := paperQVZeroLocusGlobal D
  qVZeroLocus_eq := rfl
  logShellPacket := paperGlobalLogShellPacket
  logShellPacket_eq := rfl

/-- Summary: the realified Frobenioid, the q_v zero-locus divisor and the
finite global log-shell packet are constructed; the full log-Kummer on
1,circ U_Q is assembled from the constructed finite data and the two named
missing inputs (archimedean log-shell and Kummer evaluation square). -/
theorem s1927_global_objects_and_firstMissing (D : S1895PaperInput) :
    And ((s1927ConstructedGlobalObjects D).frobenioid =
        paperGlobalRealifiedFrobenioid D)
      (And ((s1927ConstructedGlobalObjects D).qVZeroLocus =
          paperQVZeroLocusGlobal D)
        (And ((s1927ConstructedGlobalObjects D).logShellPacket =
            paperGlobalLogShellPacket)
          ((h : S1927FirstMissing D) ->
            (sq : S1927KummerEvaluationSquareActual D) ->
              Nonempty (S1927FullLogKummerUQ D)))) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h sq
  exact ⟨s1927FullLogKummerUQ_of_missing D h sq⟩

/-! ## 7. Axiom probes -/

#print axioms paperGlobalRealifiedFrobenioid
#print axioms paperGlobalRealifiedFrobenioid_divisorMonoid
#print axioms paperGlobalRealifiedFrobenioid_groupCompletion
#print axioms paperQVZeroLocusGlobal_eq_sum
#print axioms paperGlobalLogShellPacket_eq_span
#print axioms paperGlobalLogShellTensorPacket_span_eq
#print axioms s1927_global_objects_and_firstMissing

end LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual

end
