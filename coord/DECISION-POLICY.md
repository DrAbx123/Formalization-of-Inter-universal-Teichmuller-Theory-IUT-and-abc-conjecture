# Decision policy (autonomous execution, 2026-10-24)

User delegated execution and noted conflicting instructions. This file resolves conflicts in favor of SHEAF + the paper route.

## Priority when instructions conflict

1. Paper-faithful N8 target (`C9-TARGET-V3` + P6) over legacy/simplified target.
2. Named-sorry statement/dependency closure over zero-sorry/interface closure.
3. Actual source objects or exact named gap over free fields/arbitrary sets.
4. Reuse existing declarations over re-proving.
5. Off-route old Layer0/Layer1/ABC work only when a current N8 consumer needs a donor.
6. Target changes require an explicit record and reopen affected nodes; no target change by convenience.

## Active target

- Paper N8: P6 source double-construction + C9 Q/Theta/Values + paper C10.
- Status: open; Wave1 components green; Wave2 in progress.
- Legacy `N8FullOutput` closure: archived, not counted.

## Closure reporting

Every result states: target class, files/hash, named sorries, simplifications, target_accepted.

## Next automatic waves

- Wave2: C9PaperClosure/PaperN8Closure + actual/no-go attempts.
- Wave3: paper C10 assembly; easy open nodes with single donor gap; then P0/P1/P6 source objects.
- Wave4: only after N8: downstream 3.11/3.12/ABC, if route manifest confirms consumers.
