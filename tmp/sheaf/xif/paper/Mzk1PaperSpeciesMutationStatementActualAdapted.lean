import Mathlib

/-!
# Mzk1PaperSpeciesMutationStatementActualAdapted (adapted copy, A475 reuse) — paper §4 four-triangle species/mutation diagram (skeleton)

Node: routes:four_triangle_species (statement; PENDING-VERIFY). Source: [IUTchIII] §4;
paper-routes fragment (hull) official Stage 1-5 + §4 species/mutation diagram.
Registers species labels and mutation-diagram obligations as structural data only.
NO proof, NO sorry, NO axiom, NO fake closure. Citable = EXIT0 + checker.

Documentation: species = BPS / etHT / mlt / HDD / SHE / IPL / APT / q-pilot / Theta-pilot;
mutation diagram obligations connect them (paper-content named).
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperSpeciesMutationStatementActualAdapted

/-- Paper species labels (§4 four-triangle species/mutation diagram). -/
inductive PaperSpecies
  | bps | etHT | mlt | hdd | she | ipl | apt | qPilot | thetaPilot
  deriving DecidableEq, Repr

/-- Species index. -/
def PaperSpecies.index : PaperSpecies -> Nat
  | .bps => 0 | .etHT => 1 | .mlt => 2 | .hdd => 3 | .she => 4
  | .ipl => 5 | .apt => 6 | .qPilot => 7 | .thetaPilot => 8

/-- Species index bound (genuine). -/
theorem PaperSpecies.index_lt_nine (s : PaperSpecies) : s.index < 9 := by
  cases s <;> decide

/-- Mutation diagram edge obligation (paper-scope placeholder; content named). -/
structure MutationObligation (src tgt : PaperSpecies) (mutation : Prop) : Prop where
  mutationContent : mutation

end LeanFormal.IUT.XiFPaper.Mzk1PaperSpeciesMutationStatementActualAdapted
