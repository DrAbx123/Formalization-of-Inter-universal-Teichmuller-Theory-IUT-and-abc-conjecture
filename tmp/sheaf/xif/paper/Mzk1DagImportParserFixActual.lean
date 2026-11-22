/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# A783 graph import-parser fix: `public import` (mainline)

`tools/dag_build.mjs` / `dag_build_incr.mjs` parsed imports with `^\s*import`, which
does NOT match Lean's new module-system syntax `public import` (and private/protected).
As a result 425 `public import` edges were missing from the DAG: e.g.
`Pi1/Orbifold/EtaleGalois.lean` (a `module` file with `public import
Pi1.FundamentalGroup.GenericPoint`) never pulled its dependencies into the closure, so
those oleans were never scheduled and the consumer failed forever with missing olean.

Fix: regex is now `^\s*(?:public|private|protected)?\s*import\s+([A-Za-z0-9_.]+)`.

Effect: files 25622, edges 50827 (+331), closure 2193 (+118), dirty 680; all Wall-chain
files (`Iut/Cor312/{LeftHandSide,RightHandSide,Statement}`, `Iut/Concrete/ThetaRegion`,
`Iut/Wall/{Pilots,EtaAlg}`, `Iut/MainTheorem`) became dirty and schedulable.

No Lean statement/content changed. ABC gate NOT passed. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DagImportParserFixActual

def parserFixRows : List (String × String) :=
  [ ("public import lines matched", "425"),
    ("regex", "^\\s*import -> ^\\s*(?:public|private|protected)?\\s*import"),
    ("edges", "+331"),
    ("closure", "+118"),
    ("scope", "graph scheduling only; no Lean statement change; ABC gate NOT passed") ]

theorem parserFixRows_length : parserFixRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DagImportParserFixActual

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1DagImportParserFixActual.parserFixRows_length