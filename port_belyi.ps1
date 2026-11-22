$dim = Get-Content "tmp/vendor_clone_belyi/Belyi/Dimension.lean"
$ram = Get-Content "tmp/vendor_clone_belyi/Belyi/Ramification.lean"
$ns = "LeanFormal.IUT.XiFPaper.BelyiRamification"
$header = @(
"/- PORTED DONOR FILE (grace): tmp/vendor_clone_belyi/Belyi/Dimension.lean + Belyi/Ramification.lean (LANA project, Apache-2.0).",
   Changes only: namespace -> LeanFormal.IUT.XiFPaper.BelyiRamification; imports rewritten to Mathlib (the donor import Belyi.Dimension is inlined below). No math content change.",
   Route use: branch(phi) subset {0,1,infty} for B1; ramification divisor argument for B3 (route L334). -/",
"import Mathlib.AlgebraicGeometry.Stalk",
"import Mathlib.AlgebraicGeometry.Properties",
"import Mathlib.AlgebraicGeometry.Noetherian",
"import Mathlib.AlgebraicGeometry.Over",
"import Mathlib.AlgebraicGeometry.Morphisms.FiniteType",
"import Mathlib.AlgebraicGeometry.Morphisms.Etale",
"import Mathlib.AlgebraicGeometry.Morphisms.Smooth",
"import Mathlib.AlgebraicGeometry.Morphisms.Finite",
"import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap",
"import Mathlib.AlgebraicGeometry.FunctionField",
"import Mathlib.RingTheory.Smooth.Field",
"import Mathlib.RingTheory.KrullDimension.Basic",
"import Mathlib.Topology.NoetherianSpace",
"import Mathlib.Tactic",
"")
$body = @()
$body += $dim[28..]
$body += ""
$body += $ram[61..]
$body = $body | ForEach-Object { if ($_ -eq "namespace Belyi") { "namespace $ns" } elseif ($_ -eq "end Belyi") { "end $ns" } else { $_ } }
$prints = @("", "#print axioms $ns.branch_comp_subset", "#print axioms $ns.ram_comp_subset", "#print axioms $ns.finite_ram", "#print axioms $ns.finite_branch", "#print axioms $ns.ram_eq_empty_iff_etale", "#print axioms $ns.isClosed_ram")
$out = $header + $body + $prints
Set-Content -Path "tmp/sheaf/xif/paper/Mzk1G1BelyiRamificationActual.lean" -Value $out -Encoding UTF8
Write-Host ("written lines: " + (Get-Content "tmp/sheaf/xif/paper/Mzk1G1BelyiRamificationActual.lean").Count)
node tools/wd_add.mjs tmp/sheaf/xif/paper/Mzk1G1BelyiRamificationActual.lean