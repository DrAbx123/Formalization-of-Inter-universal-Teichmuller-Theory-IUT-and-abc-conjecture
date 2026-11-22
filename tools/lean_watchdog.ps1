param(
  [int]$IntervalSeconds = 30
)
$root = 'D:\lean'
$log = Join-Path $root 'tmp\lean_watchdog.log'
$targets = @(
  'tmp/sheaf/n8/closure/C1SourceDegreeGate.lean',
  'tmp/sheaf/n8/closure/C1SourceDegreeAxiomGate.lean',
  'tmp/sheaf/n8/closure/NativeSourceAssembly.lean'
)
$last = @{}
function Write-Log([string]$text) {
  $stamp = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'
  Add-Content -LiteralPath $log -Value ("[" + $stamp + "] " + $text)
}
Write-Log 'watchdog started'
while ($true) {
  foreach ($rel in $targets) {
    $path = Join-Path $root $rel
    if (-not (Test-Path -LiteralPath $path)) { continue }
    $hash = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash
    if ($last.ContainsKey($rel) -and $last[$rel] -eq $hash) { continue }
    $last[$rel] = $hash
    if ($rel -like '*AxiomGate.lean') {
      $out = & lake env lean -j1 -R $root (Join-Path 'tmp' 'sheaf\n8\closure\C1SourceDegreeAxiomGate.lean') 2>&1
      Write-Log ('AXIOM EXIT=' + $LASTEXITCODE + ' file=' + $rel)
      if ($out) { $out | Add-Content -LiteralPath $log }
    } elseif ($rel -like '*C1SourceDegreeGate.lean') {
      $olean = Join-Path $root '.lake\build\lib\lean\tmp\sheaf\n8\closure\C1SourceDegreeGate.olean'
      $out = & lake env lean -j1 -R $root -o $olean (Join-Path 'tmp' 'sheaf\n8\closure\C1SourceDegreeGate.lean') 2>&1
      Write-Log ('GATE EXIT=' + $LASTEXITCODE + ' file=' + $rel)
      if ($out) { $out | Add-Content -LiteralPath $log }
    } else {
      $out = & lake env lean -j1 -R $root -o (Join-Path $root ('.lake\build\lib\lean\' + [IO.Path]::ChangeExtension($rel,'olean'))) (Join-Path $root $rel) 2>&1
      Write-Log ('ASSEMBLY EXIT=' + $LASTEXITCODE + ' file=' + $rel)
      if ($out) { $out | Add-Content -LiteralPath $log }
    }
  }
  Start-Sleep -Seconds $IntervalSeconds
}
