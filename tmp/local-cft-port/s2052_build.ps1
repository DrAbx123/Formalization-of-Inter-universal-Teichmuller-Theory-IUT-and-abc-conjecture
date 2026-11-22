$ErrorActionPreference = 'Continue'
$log = 'D:\lean\tmp\local-cft-port\_s2052_build.log'
$mods = @(
  'ClassFieldAxiom.Coordinates',
  'ClassFieldAxiom.Approximation',
  'ClassFieldAxiom.Lattice',
  'ClassFieldAxiom.Units',
  'ClassFieldAxiom.Vanishing',
  'ClassFieldAxiom.HerbrandUnits',
  'ClassFieldAxiom.Axiom',
  'Reciprocity.SecondInequality',
  'Reciprocity.Standard',
  'Reciprocity.UnitIndex',
  'Reciprocity.UnitMap',
  'Reciprocity.LevelMap',
  'Reciprocity.Neukirch',
  'Reciprocity.CyclicLevel',
  'Reciprocity.Tools',
  'Reciprocity.LevelFrob',
  'Reciprocity.OmegaLevel',
  'Reciprocity.LevelNeukirch',
  'Reciprocity.Embedding',
  'Reciprocity.CyclicRec',
  'Reciprocity.Abelian',
  'Reciprocity.Artin',
  'Reciprocity.ArtinContinuous',
  'Reciprocity.Existence',
  'Reciprocity.FrobLiftPow',
  'Reciprocity.BaseChange',
  'Reciprocity.NormCompat',
  'Reciprocity.Conjugation',
  'Reciprocity.NormLimitation',
  'Reciprocity.Kummer',
  'Reciprocity.ExistenceTheorem',
  'Reciprocity.ArtinInertia',
  'Reciprocity.ArtinUnique',
  'Reciprocity.GaloisStructure',
  'Reciprocity.UnitFiltration',
  'Reciprocity.ProfiniteCompletion',
  'Reciprocity.OmegaIndependence'
)
Set-Location 'D:\lean'
"START $(Get-Date -Format o)" | Set-Content $log
foreach ($m in $mods) {
  $rel = $m.Replace('.', '\')
  $src = "tmp/local-cft-port/$rel.lean"
  $olean = ".lake/build/lib/lean/$rel.olean"
  $ok = $false
  $lastOut = ''
  for ($i = 1; $i -le 6; $i++) {
    $lastOut = (& lake build $m 2>&1 | Out-String)
    $code = $LASTEXITCODE
    if ($code -eq 0) { $ok = $true; break }
    "RETRY $m attempt=$i exit=$code" | Add-Content $log
    Start-Sleep -Seconds 12
  }
  if ($ok) {
    $sha = (Get-FileHash $src -Algorithm SHA256).Hash
    $olen = if (Test-Path $olean) { (Get-Item $olean).Length } else { -1 }
    $osha = if (Test-Path $olean) { (Get-FileHash $olean -Algorithm SHA256).Hash } else { 'NONE' }
    "OK $m EXIT=0 SHA256=$sha OLEAN_BYTES=$olen OLEAN_SHA256=$osha" | Add-Content $log
  } else {
    "FAIL $m" | Add-Content $log
    $lastOut | Add-Content $log
    break
  }
}
"ALLDONE $(Get-Date -Format o)" | Add-Content $log
