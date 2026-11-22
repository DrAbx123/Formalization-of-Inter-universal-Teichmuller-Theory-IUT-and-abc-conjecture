/-
  S2757: assembling the source completion above the concrete `l = 5` root

  Target.  Construct the canonical native initial Theta datum
  `SourceNativeInitialThetaData fiveLabel` by assembling a
  `SourceCompletion` from an actual geometric core
  `G : SourceSignQuotientGeometricCore A`, then deliver the first S2753
  carrier-transport piece.

  Exact reduction (this file, kernel-checked).

  * The geometric core plus an unconditional selected-place record supplies
    every geometric and selected-place field of
    `SourceCompletionSignQuotient` (`G.toSourceCompletionSignQuotient P`).
    No place data is read from `G`: `SourcePlaceSelection` is supplied
    unconditionally by `placeSelectionOfArithmeticData`, and
    `SourcePlaceSelection.V_section` is the canonical restriction section.
  * `SourceFbarExtension.canonical A` supplies `fbar`.
  * `SourceArithmeticPrelude.fromPlaceSection A P.V_section` supplies
    `arithmeticPrelude`, and the field
    `arithmeticPrelude.placeSection = signQuotient.V_section` is `rfl`
    because both sides are the canonical restriction section.
  * The six clause fields `clauseA ... clauseF` are NOT supplied by the
    geometric core.  They are exactly the source conditions of IUT I
    Definition 3.1(a)-(f), tracked in the repository as
    `SourceClauseAssembly A (G.toSourceSignQuotientData P)` (its six fields
    are literally `SourceClauseA ... SourceClauseF`).

  Hence a `SourceCompletion` cannot be constructed from `G` alone: any
  `SourceCompletion` yields a `SourceClauseAssembly` over its own
  arithmetic root and sign quotient
  (`S2757_clauseAssembly_of_completion`), and conversely a clause assembly
  is sufficient (`S2757CompletionOfClauseAssembly`).  The place fields,
  `fbar` and the prelude are not missing: they are constructed below
  without hypotheses.  No field is fabricated.

  What is delivered:
  * `S2757CompletionOfClauseAssembly` : exact completion constructor from
    `(A, G, P, SourceClauseAssembly A (G.toSourceSignQuotientData P))`;
  * `S2757NativeT` : the resulting `SourceNativeInitialThetaData fiveLabel`,
    conditional on exactly that clause assembly;
  * `S2757_clauseAssembly_of_completion` and
    `S2757_nonempty_sourceCompletion_iff` : the exact missing unit;
  * `S2753KEquiv` : the first S2753 carrier-transport piece at the K level
    (`(S2735Arithmetic fiveLabel).K` to `T.arithmetic.K`), conditional on
    the same clause assembly, together with the unconditional
    identification of that carrier with `GaussianField`.

  The first error of the attempted unconditional constructor is recorded in
  section 5.
-/

import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction
import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual
import tmp.sheaf.xif.paper.S2753CarrierTransportActual

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual (fiveLabel)

set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2757SourceCompletionNativeActual

/-! ## 0. The concrete root and the prime label -/

/-- The concrete prime label `l = 5` used by the S2757 line. -/
theorem fiveLabel_value : fiveLabel.value = 5 := rfl

/-- The arithmetic root of the S2735 line, at universe `0`.  It is
definitionally `S2735Arithmetic fiveLabel`
(`gaussianInitialThetaArithmeticData fiveLabel`). -/
abbrev S2753A : InitialThetaArithmeticData.{0} fiveLabel :=
  S2735Arithmetic fiveLabel

theorem S2753A_eq_S2735Arithmetic :
    S2753A = S2735Arithmetic fiveLabel := rfl

/-! ## 1. The place half, `fbar` and the prelude are unconditional -/

/-- The geometric core together with the unconditional selected-place record
supplies the whole `SourceCompletionSignQuotient`.  No place data is taken
from `G`. -/
noncomputable def S2757SignQuotient
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A) :
    SourceCompletionSignQuotient A :=
  G.toSourceCompletionSignQuotient (placeSelectionOfArithmeticData A)

theorem S2757SignQuotient_toSourceSignQuotientData
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A) :
    (S2757SignQuotient A G).toSourceSignQuotientData =
      G.toSourceSignQuotientData (placeSelectionOfArithmeticData A) := rfl

/-- The canonical algebraic closure supplies `fbar` for any arithmetic
root; this field is not part of the missing data. -/
noncomputable def S2757Fbar
    (A : InitialThetaArithmeticData.{0} fiveLabel) :
    SourceFbarExtension A :=
  SourceFbarExtension.canonical A

/-- The canonical restriction section supplies `arithmeticPrelude`; this
field is not part of the missing data. -/
noncomputable def S2757Prelude
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (P : SourcePlaceSelection A) :
    SourceArithmeticPrelude A :=
  SourceArithmeticPrelude.fromPlaceSection A P.V_section

theorem S2757Prelude_placeSection
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (P : SourcePlaceSelection A) :
    (S2757Prelude A P).placeSection = P.V_section := rfl

/-! ## 2. The completion: everything but the six clause fields

  The only input beyond `(A, G, P)` is
  `assembly : SourceClauseAssembly A (G.toSourceSignQuotientData P)`, whose
  six fields are exactly the six clause fields of `SourceCompletion`. -/

/-- Exact `SourceCompletion` constructor from the geometric core, an
arbitrary selected-place record, and the clause assembly over the induced
sign quotient. -/
noncomputable def S2757CompletionOfClauseAssembly
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (assembly : SourceClauseAssembly.{0} A (G.toSourceSignQuotientData P)) :
    SourceCompletion.{0} fiveLabel where
  arithmetic := A
  fbar := S2757Fbar A
  signQuotient := G.toSourceCompletionSignQuotient P
  arithmeticPrelude := S2757Prelude A P
  arithmeticPrelude_placeSection := rfl
  clauseA := assembly.clauseA
  clauseB := assembly.clauseB
  clauseC := assembly.clauseC
  clauseD := assembly.clauseD
  clauseE := assembly.clauseE
  clauseF := assembly.clauseF

@[simp] theorem S2757CompletionOfClauseAssembly_arithmetic
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (assembly : SourceClauseAssembly.{0} A (G.toSourceSignQuotientData P)) :
    (S2757CompletionOfClauseAssembly A G P assembly).arithmetic = A := rfl

@[simp] theorem S2757CompletionOfClauseAssembly_signQuotient
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (assembly : SourceClauseAssembly.{0} A (G.toSourceSignQuotientData P)) :
    (S2757CompletionOfClauseAssembly A G P assembly).signQuotient =
      G.toSourceCompletionSignQuotient P := rfl

@[simp] theorem S2757CompletionOfClauseAssembly_fbar
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (assembly : SourceClauseAssembly.{0} A (G.toSourceSignQuotientData P)) :
    (S2757CompletionOfClauseAssembly A G P assembly).fbar =
      SourceFbarExtension.canonical A := rfl

@[simp] theorem S2757CompletionOfClauseAssembly_arithmeticPrelude
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (assembly : SourceClauseAssembly.{0} A (G.toSourceSignQuotientData P)) :
    (S2757CompletionOfClauseAssembly A G P assembly).arithmeticPrelude =
      SourceArithmeticPrelude.fromPlaceSection A P.V_section := rfl

/-- The native initial Theta datum of the S2757 line.  Conditional exactly on
`assembly : SourceClauseAssembly A (G.toSourceSignQuotientData P)`. -/
noncomputable def S2757NativeT
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (assembly : SourceClauseAssembly.{0} A (G.toSourceSignQuotientData P)) :
    SourceNativeInitialThetaData fiveLabel :=
  (S2757CompletionOfClauseAssembly A G P assembly).toSourceNativeInitialThetaData

@[simp] theorem S2757NativeT_arithmetic
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (assembly : SourceClauseAssembly.{0} A (G.toSourceSignQuotientData P)) :
    (S2757NativeT A G P assembly).arithmetic = A := rfl

@[simp] theorem S2757NativeT_source
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (assembly : SourceClauseAssembly.{0} A (G.toSourceSignQuotientData P)) :
    (S2757NativeT A G P assembly).tuple.source =
      G.toSourceSignQuotientData P := rfl

@[simp] theorem S2757NativeT_xK
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (assembly : SourceClauseAssembly.{0} A (G.toSourceSignQuotientData P)) :
    (S2757NativeT A G P assembly).tuple.source.xK = G.xK := rfl

@[simp] theorem S2757NativeT_cK
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (assembly : SourceClauseAssembly.{0} A (G.toSourceSignQuotientData P)) :
    (S2757NativeT A G P assembly).tuple.source.cK = G.cK := rfl

/-- A `SourceCompletion` over `fiveLabel` determines a clause assembly over
its own arithmetic root and sign quotient: the six clause fields are exactly
the fields of `SourceClauseAssembly`, and the other `SourceCompletion`
fields are constructed unconditionally in section 1. -/
theorem S2757_clauseAssembly_of_completion
    (C : SourceCompletion.{0} fiveLabel) :
    Nonempty (SourceClauseAssembly.{0} C.arithmetic
      C.signQuotient.toSourceSignQuotientData) :=
  ⟨{ clauseA := C.clauseA
     clauseB := C.clauseB
     clauseC := C.clauseC
     clauseD := C.clauseD
     clauseE := C.clauseE
     clauseF := C.clauseF }⟩

/-- Exact form of the missing unit: a `SourceCompletion` over `fiveLabel`
exists exactly when there are an arithmetic root and a sign quotient carrying
a clause assembly.  The sufficiency direction uses the unconditional `fbar`
and prelude of section 1; the necessity direction is
`S2757_clauseAssembly_of_completion`. -/
theorem S2757_nonempty_sourceCompletion_iff :
    Nonempty (SourceCompletion.{0} fiveLabel) ↔
      ∃ (A : InitialThetaArithmeticData.{0} fiveLabel)
        (SQ : SourceSignQuotientData.{0} A),
        Nonempty (SourceClauseAssembly.{0} A SQ) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.arithmetic, C.signQuotient.toSourceSignQuotientData,
      S2757_clauseAssembly_of_completion C⟩
  · rintro ⟨A, SQ, ⟨assembly⟩⟩
    exact ⟨{ arithmetic := A
             fbar := SourceFbarExtension.canonical A
             signQuotient := SourceCompletionSignQuotient.ofSourceSignQuotientData SQ
             arithmeticPrelude := SourceArithmeticPrelude.fromPlaceSection A SQ.V_section
             arithmeticPrelude_placeSection := rfl
             clauseA := assembly.clauseA
             clauseB := assembly.clauseB
             clauseC := assembly.clauseC
             clauseD := assembly.clauseD
             clauseE := assembly.clauseE
             clauseF := assembly.clauseF }⟩

/-! ## 3. The exact missing fields

  Relative to `(A, G)` the fields of `SourceCompletion` split as:

  | field | status |
  | --- | --- |
  | arithmetic | given |
  | fbar | constructed (SourceFbarExtension.canonical) |
  | signQuotient | constructed from G and the unconditional place record |
  | arithmeticPrelude | constructed (fromPlaceSection, restriction section) |
  | arithmeticPrelude_placeSection | rfl |
  | clauseA | missing, SourceClauseA A (G.toSourceSignQuotientData P) |
  | clauseB | missing, SourceClauseB A ... clauseA |
  | clauseC | missing, SourceClauseC A ... clauseA clauseB |
  | clauseD | missing, SourceClauseD A ... clauseA clauseB clauseC |
  | clauseE | missing, SourceClauseE A ... clauseA clauseB clauseC clauseD |
  | clauseF | missing, SourceClauseF A ... clauseA clauseB clauseC clauseD clauseE |

  The missing part is exactly one term of
  `SourceClauseAssembly A (G.toSourceSignQuotientData P)`.  See section 5 for
  the recorded first error of the attempted unconditional constructor. -/

/-! ## 4. S2753 first carrier transport piece -/

/-- The S2735 carrier is definitionally the Gaussian field. -/
theorem S2753A_K_eq_GaussianField : S2753A.K = GaussianField := rfl

/-- The S2735 carrier is definitionally the K carrier of the S2735
arithmetic root. -/
theorem S2753A_K_eq_S2735Arithmetic :
    S2753A.K = (S2735Arithmetic fiveLabel).K := rfl

/-- First S2753 carrier-transport piece: the K-level ring equivalence between
the S2735 arithmetic carrier and the native datum carrier, for any native
datum `S2757NativeT S2753A G P assembly`.  Because the native datum keeps its
arithmetic root definitionally (`S2757NativeT_arithmetic`), this is
`RingEquiv.refl` on the common carrier; it is not a fabricated equivalence.

  Caveat (checked separately in `tmp/sheaf/xif/paper/_S2753Probe.lean`,
  `noGaussianNativeT`): over `S2753A` clause (c) is unsatisfiable because the
  identity tower `Fmod = F = K` forces a trivial `l`-torsion representation
  while clause (c) also requires an `SL₂` image.  Hence the assembly
  hypothesis of this definition is empty at `S2753A`; the definition is the
  exact conditional carrier transport, not an existence claim over
  `S2753A`. -/
noncomputable def S2753KEquiv
    (G : SourceSignQuotientGeometricCore S2753A)
    (P : SourcePlaceSelection S2753A)
    (assembly : SourceClauseAssembly.{0} S2753A (G.toSourceSignQuotientData P)) :
    (S2735Arithmetic fiveLabel).K ≃+*
      (S2757NativeT S2753A G P assembly).arithmetic.K :=
  RingEquiv.refl ((S2735Arithmetic fiveLabel).K)

theorem S2753KEquiv_apply
    (G : SourceSignQuotientGeometricCore S2753A)
    (P : SourcePlaceSelection S2753A)
    (assembly : SourceClauseAssembly.{0} S2753A (G.toSourceSignQuotientData P))
    (x : (S2735Arithmetic fiveLabel).K) :
    S2753KEquiv G P assembly x = x := rfl

theorem S2753KEquiv_symm_apply
    (G : SourceSignQuotientGeometricCore S2753A)
    (P : SourcePlaceSelection S2753A)
    (assembly : SourceClauseAssembly.{0} S2753A (G.toSourceSignQuotientData P))
    (x : (S2735Arithmetic fiveLabel).K) :
    (S2753KEquiv G P assembly).symm x = x := rfl

#print axioms S2757CompletionOfClauseAssembly
#print axioms S2757NativeT
#print axioms S2757_clauseAssembly_of_completion
#print axioms S2757_nonempty_sourceCompletion_iff
#print axioms S2753KEquiv

/-! ## 5. Recorded first error of the unconditional attempt

  The parent-requested definition

  `noncomputable def S2757Completion
      (G : SourceSignQuotientGeometricCore S2753A) :
      SourceCompletion.{0} fiveLabel`

  was compiled as a probe with every non-clause field assigned exactly as in
  `S2757CompletionOfClauseAssembly` and no clause fields.  It fails, and the
  failure is exactly the missing unit of section 3.

  Probe source of the structure literal:

  ```
  noncomputable def S2757Completion
      (G : SourceSignQuotientGeometricCore S2753A) :
      SourceCompletion.{0} fiveLabel where
    arithmetic := S2753A
    fbar := SourceFbarExtension.canonical S2753A
    signQuotient := G.toSourceCompletionSignQuotient
      (placeSelectionOfArithmeticData S2753A)
    arithmeticPrelude := SourceArithmeticPrelude.fromPlaceSection S2753A
      (placeSelectionOfArithmeticData S2753A).V_section
    arithmeticPrelude_placeSection := rfl
  ```

  EXACT FIRST ERROR (verbatim; probe compile, exit code 1, the only error in
  the file; line 323 is the line of the structure literal in the probe
  version):

    tmp/sheaf/xif/paper/S2757SourceCompletionNativeActual.lean:323:35: error: Fields missing: `clauseA`, `clauseB`, `clauseC`, `clauseD`, `clauseE`, `clauseF`

  No error was reported for `arithmetic`, `fbar`, `signQuotient`,
  `arithmeticPrelude` or `arithmeticPrelude_placeSection`: those five fields
  are exactly the ones constructed unconditionally in section 1.  The six
  missing fields are exactly the fields of
  `SourceClauseAssembly A (G.toSourceSignQuotientData P)`.  No field is
  fabricated in this file. -/

end LeanFormal.IUT.XiFPaper.S2757SourceCompletionNativeActual

end


namespace LeanFormal.IUT.XiFPaper.S2757SourceCompletionNativeActual

/-- Re-export the S2753 canonical-fiveLabel Gaussian no-go. -/
def S2757_noGaussianNativeT_fiveLabel :=
  LeanFormal.IUT.XiFPaper.S2753CarrierTransportActual.noGaussianNativeT

end LeanFormal.IUT.XiFPaper.S2757SourceCompletionNativeActual
