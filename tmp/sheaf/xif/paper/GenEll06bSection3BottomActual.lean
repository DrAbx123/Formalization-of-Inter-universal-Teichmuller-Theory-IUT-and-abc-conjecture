import Mathlib
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GenEll06bSection3BottomActual

/-- Lemma 3.1 (i) generator alpha = [[1,1],[0,1]] in SL2(Z/l) for a prime l (corpus
lines 762-778; part of the tree of well-known facts on SL2 used for Thm 3.8). -/
def belyiAlpha (l : Nat) [Fact l.Prime] : Matrix.SpecialLinearGroup (Fin 2) (ZMod l) :=
  ⟨!![1, 1; 0, 1], by
    rw [Matrix.det_fin_two]
    simp⟩

/-- Lemma 3.1 (i) generator beta = [[1,0],[1,1]] in SL2(Z/l). -/
def belyiBeta (l : Nat) [Fact l.Prime] : Matrix.SpecialLinearGroup (Fin 2) (ZMod l) :=
  ⟨!![1, 0; 1, 1], by
    rw [Matrix.det_fin_two]
    simp⟩

/-- Lemma 3.1(i) exact statement (corpus 762-778): alpha and beta generate SL2(F_l)
for prime l.  Registered as the paper's well-known-facts input (class B; the actual
generation proof for ZMod l is not formalized). -/
def Lemma31SL2GenerationPaperInput (l : Nat) [Fact l.Prime] : Prop :=
  ∀ x : Matrix.SpecialLinearGroup (Fin 2) (ZMod l),
    x ∈ Subgroup.closure ({belyiAlpha l, belyiBeta l} :
      Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod l)))

/-- Paper-input registration record for GenEll section 3 bottom layer: Lemma 3.1
(structure of SL2) and Theorem 3.8 (full special linear Galois action) with corpus
lines; the deep Faltings/Serre-type input remains a named paper input. -/
def s3135Section3BottomStatus : Audit.Obligation :=
  { id := "GENELL.P2.sec3-sl2-bottom"
    source :=
      "papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt " ++
        "section 3 lines 738-1199 (Lemma 3.1 :762-800; Prop 3.4; Lemma 3.5/3.6/3.7; " ++
        "Theorem 3.8)"
    status := Audit.VerificationStatus.interface
    note :=
      "CLASS A DONE HERE: the concrete generators alpha=[[1,1],[0,1]] and " ++
        "beta=[[1,0],[1,1]] are constructed as elements of " ++
        "Matrix.SpecialLinearGroup (Fin 2) (ZMod l) with det=1 proofs (Mathlib).  " ++
        "CLASS B NAMED (paper inputs, not proved): Lemma 3.1(i) generation " ++
        "Lemma31SL2GenerationPaperInput; Lemma 3.1(ii) no nontrivial abelian " ++
        "quotients; Lemma 3.1(iii)/(iv) subgroup criteria; Prop 3.4 (Faltings " ++
        "heights); Lemma 3.5/3.6/3.7; Theorem 3.8 (full SL2 Galois action, deep " ++
        "Faltings/Serre-type input, corpus ~1100-1199).  No upper-layer advance; " ++
        "registry frozen 14041; no registry edits."
    dependsOn := [ "GENELL.P0", "EXPEST.01" ]
    sorryItems :=
      [ "Lemma 3.1(i)-(iv) SL2 structure facts (class B)",
        "Prop 3.4 Faltings heights (class B)",
        "Lemma 3.5/3.6/3.7 (class B)",
        "Theorem 3.8 full SL2 Galois action (class B deep input)" ] }

#check belyiAlpha
#check belyiBeta
#check Lemma31SL2GenerationPaperInput
end LeanFormal.IUT.XiFPaper.GenEll06bSection3BottomActual
end
-- recompile-bump-20261110-0644
-- recompile-bump-3
