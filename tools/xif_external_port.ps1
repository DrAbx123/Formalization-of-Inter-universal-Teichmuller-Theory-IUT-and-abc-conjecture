<#
.SYNOPSIS
  Analyze import chain of external Lean targets, port only that closure, compile in dependency order (explicit only).
.DESCRIPTION
  -Analyze : write import_chain.md (version diff, reference trees, topological order, mathlib imports, missing). No copy, no compile.
  -Port    : copy closure to <PortRoot>/<Name>, rewrite internal imports, drop missing Mathlib imports, attribution header, apply rules.
  -Compile : compile ported files in dependency order (fresh skip, first errors, skip dependents of failures). Use with -Port or after -Port.
.EXAMPLE
  tools/xif_external_port.ps1 -Name flt -Targets 'a.lean;b.lean' -Analyze
#>
param(
  [string]$Name = 'flt',
  [string]$SrcRoot = 'D:\lean\tmp\external\flt-lean',
  [string]$OurRoot = 'D:\lean',
  [string[]]$Targets = @(),
  [string]$PortRoot = 'D:\lean\tmp\external\ported',
  [switch]$Analyze,
  [switch]$Port,
  [switch]$Compile,
  [int]$MaxErrorLines = 4,
  [switch]$KeepGoing,
  [string]$Rules = 'D:\lean\tools\port_fix_rules.txt'
)
$ErrorActionPreference = 'Continue'
$nl = [Environment]::NewLine
$Targets = @($Targets | ForEach-Object { $_ -split '[,;]' } | ForEach-Object { $_.Trim() } | Where-Object { $_.Length -gt 0 })
if (-not ($Analyze -or $Port -or $Compile)) { $Analyze = $true }
$outRoot = Join-Path $PortRoot $Name
New-Item -ItemType Directory -Force -Path $outRoot | Out-Null
$repoUrl = 'unknown'
$srcRev = ''
if (Test-Path (Join-Path $SrcRoot '.git')) {
  $repoUrl = ((& git -C $SrcRoot remote get-url origin 2>$null) | Out-String).Trim()
  $srcRev = ((& git -C $SrcRoot rev-parse --short HEAD 2>$null) | Out-String).Trim()
}
$srcLean = ((Get-Content (Join-Path $SrcRoot 'lean-toolchain') -ErrorAction SilentlyContinue) | Out-String).Trim()
$ourLean = ((Get-Content (Join-Path $OurRoot 'lean-toolchain') -ErrorAction SilentlyContinue) | Out-String).Trim()
function GetMathlibRev([string]$root) {
  $p = Join-Path $root 'lake-manifest.json'
  if (-not (Test-Path $p)) { return '(no manifest)' }
  try {
    $j = Get-Content $p -Raw | ConvertFrom-Json
    $pkg = $j.packages | Where-Object { $_.name -eq 'mathlib' } | Select-Object -First 1
    if ($pkg) { return [string]$pkg.rev }
    return '(mathlib not in manifest)'
  } catch { return '(manifest parse error)' }
}
function GetImports([string]$path) {
  $res = @()
  $ls = Get-Content -LiteralPath $path -Encoding UTF8  -ErrorAction SilentlyContinue
  foreach ($l in $ls) {
    $t = $l.Trim()
    if ($t -match '^(public |private |protected )?import (.+)$') {
      $rest = $Matches[2].Trim()
      foreach ($m in ($rest -split '\s+')) { if ($m.Length -gt 0) { $res = $res + $m } }
    }
  }
  return $res
}
function ResolveModule([string]$mod) {
  $rel = ($mod -replace '\.', '/') + '.lean'
  $full = Join-Path $SrcRoot $rel
  if (Test-Path $full) { return $rel }
  return $null
}
function IsExt([string]$m) {
  if ($m.StartsWith('Mathlib')) { return $true }
  if ($m.StartsWith('Lean')) { return $true }
  if ($m.StartsWith('Std')) { return $true }
  if ($m.StartsWith('Batteries')) { return $true }
  if ($m.StartsWith('Aesop')) { return $true }
  if ($m.StartsWith('Qq')) { return $true }
  if ($m.StartsWith('Plausible')) { return $true }
  if ($m.StartsWith('ProofWidgets')) { return $true }
  return $false
}
$deps = @{}
$mlImports = @{}
$sizes = @{}
$visited = @{}
$order = New-Object System.Collections.Generic.List[string]
$missing = New-Object System.Collections.Generic.List[string]
function Visit([string]$rel) {
  if ($visited.ContainsKey($rel)) { return }
  $visited[$rel] = $true
  $abs = Join-Path $SrcRoot $rel
  $d = @()
  $ml = @()
  foreach ($imp in (GetImports $abs)) {
    if (IsExt $imp) { $ml = $ml + $imp; continue }
    $r = ResolveModule $imp
    if ($r) { $d = $d + $r; Visit $r } else { $missing.Add($rel + ' -> ' + $imp) | Out-Null }
  }
  $deps[$rel] = $d
  $mlImports[$rel] = $ml
  $sizes[$rel] = (Get-Item $abs).Length
  $order.Add($rel) | Out-Null
}
if ($Targets.Count -eq 0) { Write-Output 'ERROR: -Targets required'; exit 1 }
foreach ($t in $Targets) {
  $t2 = $t -replace '\\', '/'
  $full = Join-Path $SrcRoot $t2
  if (-not (Test-Path $full)) { $missing.Add('TARGET NOT FOUND: ' + $t2) | Out-Null; continue }
  Visit $t2
}
$depth = @{}
function GetDepth([string]$rel) {
  if ($depth.ContainsKey($rel)) { return $depth[$rel] }
  $d = 0
  foreach ($x in $deps[$rel]) {
    $dd = (GetDepth $x) + 1
    if ($dd -gt $d) { $d = $dd }
  }
  $depth[$rel] = $d
  return $d
}
foreach ($rel in $order) { [void](GetDepth $rel) }
function RenderTree([string]$rel, [string]$indent) {
  $s = New-Object System.Collections.Generic.List[string]
  $s.Add($indent + '- ' + $rel + ' (' + $sizes[$rel] + 'B)')
  foreach ($x in $deps[$rel]) {
    foreach ($l in (RenderTree $x ($indent + '    '))) { $s.Add($l) }
  }
  return $s
}
$R = New-Object System.Collections.Generic.List[string]
$R.Add('# Import chain analysis: ' + $Name)
$R.Add('')
$R.Add('Generated: ' + (Get-Date -Format 'yyyy-MM-dd HH:mm:ss'))
$R.Add('')
$R.Add('## Version diff')
$R.Add('')
$R.Add('- external repo: ' + $repoUrl + ' @ ' + $srcRev)
$R.Add('- external lean-toolchain: ' + $srcLean + ' | our lean-toolchain: ' + $ourLean)
$R.Add('- external mathlib rev: ' + (GetMathlibRev $SrcRoot) + ' | our mathlib rev: ' + (GetMathlibRev $OurRoot))
$R.Add('')
$R.Add('## Targets and reference chains')
$R.Add('')
foreach ($t in $Targets) {
  $t2 = $t -replace '\\', '/'
  if (-not $visited.ContainsKey($t2)) { continue }
  $R.Add('### ' + $t2)
  $R.Add('')
  foreach ($l in (RenderTree $t2 '')) { $R.Add($l) }
  $R.Add('')
}
$R.Add('## Topological order (dependencies first)')
$R.Add('')
$R.Add('| # | depth | file | size | internal deps | mathlib imports |')
$R.Add('|---|---|---|---|---|---|')
$i = 0
foreach ($rel in $order) {
  $i = $i + 1
  $R.Add('| ' + $i + ' | ' + $depth[$rel] + ' | ' + $rel + ' | ' + $sizes[$rel] + ' | ' + $deps[$rel].Count + ' | ' + $mlImports[$rel].Count + ' |')
}
$R.Add('')
$R.Add('## Mathlib imports per file')
$R.Add('')
foreach ($rel in $order) {
  if ($mlImports[$rel].Count -gt 0) { $R.Add('- ' + $rel + ': ' + ($mlImports[$rel] -join ', ')) }
}
$R.Add('')
$R.Add('## Missing prerequisites')
$R.Add('')
$um = @($missing | Select-Object -Unique)
if ($um.Count -eq 0) { $R.Add('(none)') } else { foreach ($m in $um) { $R.Add('- ' + $m) } }
$R.Add('')
$R.Add('## Summary')
$R.Add('')
$tot = 0
foreach ($x in $order) { $tot = $tot + $sizes[$x] }
$md = 0
foreach ($x in $order) { if ($depth[$x] -gt $md) { $md = $depth[$x] } }
$R.Add('- files in closure: ' + $order.Count)
$R.Add('- total bytes: ' + $tot)
$R.Add('- max depth: ' + $md)
Set-Content -LiteralPath (Join-Path $outRoot 'import_chain.md') -Value ($R -join $nl) -Encoding utf8
Write-Output ('ANALYZED targets=' + $Targets.Count + ' files=' + $order.Count + ' missing=' + $um.Count)
Write-Output ('CHAIN_REPORT=' + (Join-Path $outRoot 'import_chain.md'))
if ($Port) {
  $prefix = 'tmp.external.ported.' + $Name
  foreach ($rel in $order) {
    $abs = Join-Path $SrcRoot $rel
    $dest = Join-Path $outRoot $rel
    $destDir = Split-Path $dest
    if (-not (Test-Path $destDir)) { New-Item -ItemType Directory -Force -Path $destDir | Out-Null }
    $importLines = New-Object System.Collections.Generic.List[string]
    $bodyLines = New-Object System.Collections.Generic.List[string]
    foreach ($l in (Get-Content -LiteralPath $abs -Encoding UTF8)) {
      $t = $l.Trim()
      if ($t -match '^(public |private |protected )?import (.+)$') {
        $prefixOut = $Matches[1]; if ($null -eq $prefixOut) { $prefixOut = '' }
        $mods = ($Matches[2].Trim() -split '\s+') | Where-Object { $_.Length -gt 0 }
        $newMods = @()
        foreach ($m in $mods) {
          if (IsExt $m) { $newMods = $newMods + $m; continue }
          $r = ResolveModule $m
          if ($r -and $visited.ContainsKey($r)) { $newMods = $newMods + ($prefix + '.' + $m) }
          else { $newMods = $newMods + $m; $missing.Add($rel + ' -> unresolved import ' + $m) | Out-Null }
        }
        $importLines.Add($prefixOut + 'import ' + ($newMods -join ' '))
      } else { $bodyLines.Add($l) }
    }
    $moduleLine = ''
    for ($k = 0; $k -lt $bodyLines.Count; $k++) { if ($bodyLines[$k].Trim() -eq 'module') { $moduleLine = $bodyLines[$k]; $bodyLines.RemoveAt($k); break } }
    $out = New-Object System.Collections.Generic.List[string]
    if ($moduleLine -ne '') { $out.Add($moduleLine) }
    foreach ($il in $importLines) { $out.Add($il) }
    $out.Add('')
    $out.Add('/-! Ported for reuse from ' + $repoUrl + ' (commit ' + $srcRev + '), file ' + $rel + '. License: see source repo LICENSE (Apache-2.0); attribution retained. Imports rewritten for local Mathlib ' + $ourLean + '. -/')
    $out.Add('')
    foreach ($bl in $bodyLines) { $out.Add($bl) }
    [System.IO.File]::WriteAllText($dest, (($out -join $nl) + $nl), (New-Object System.Text.UTF8Encoding($false)))
  }
  $ruleList = @()
  if (Test-Path $Rules) {
    foreach ($ln in (Get-Content -LiteralPath $Rules)) {
      if ($ln.Trim().Length -eq 0) { continue }
      if ($ln.Trim().StartsWith('#')) { continue }
      $parts = $ln -split '\|\|', 2
      if ($parts.Count -eq 2) { $ruleList = $ruleList + ,@($parts[0], $parts[1]) }
    }
  }
  $applied = 0
  if ($ruleList.Count -gt 0) {
    foreach ($rel in $order) {
      $dest = Join-Path $outRoot $rel
      $txt = Get-Content -LiteralPath $dest -Raw -Encoding UTF8
      $orig = $txt
      foreach ($rule in $ruleList) { try { $txt = [regex]::Replace($txt, $rule[0], $rule[1]) } catch { } }
      if ($txt -ne $orig) { [System.IO.File]::WriteAllText($dest, $txt, (New-Object System.Text.UTF8Encoding($false))); $applied = $applied + 1 }
    }
  }
  Set-Content -LiteralPath (Join-Path $outRoot 'topo_order.txt') -Value ($order | ForEach-Object { $prefix.Replace('.', '/') + '/' + $_ }) -Encoding utf8
  foreach ($rel in $order) {
    $oleRel = $rel -replace '\.lean$', '.olean'
    $oleDir = Join-Path (Join-Path $OurRoot '.lake\build\lib\lean') (Split-Path ($prefix.Replace('.', '/') + '/' + $oleRel))
    if (-not (Test-Path $oleDir)) { New-Item -ItemType Directory -Force -Path $oleDir | Out-Null }
  }
  Write-Output ('PORTED files=' + $order.Count + ' rules=' + $ruleList.Count + ' patched=' + $applied + ' out=' + $outRoot)
}
if ($Compile) {
  $failed = @{}
  $failedMsgs = @{}
  $C = New-Object System.Collections.Generic.List[string]
  $C.Add('# Compile report: ' + $Name)
  $C.Add('')
  $C.Add('| # | file | status |')
  $C.Add('|---|---|---|')
  $i = 0
  foreach ($rel in $order) {
    $i = $i + 1
    $dest = Join-Path $outRoot $rel
    if (-not (Test-Path $dest)) { $C.Add('| ' + $i + ' | ' + $rel + ' | NOT PORTED |'); continue }
    $blocked = $false
    foreach ($d in $deps[$rel]) { if ($failed.ContainsKey($d) -and -not $KeepGoing) { $blocked = $true } }
    if ($blocked) { $C.Add('| ' + $i + ' | ' + $rel + ' | SKIPPED(dep-failed) |'); continue }
    $portRel = ([System.IO.Path]::GetRelativePath($OurRoot, $dest)) -replace '\\', '/'
    $olean = Join-Path (Join-Path $OurRoot '.lake\build\lib\lean') ($portRel -replace '\.lean$', '.olean')
    $fresh = $false
    if (Test-Path $olean) { $fresh = ((Get-Item $olean).LastWriteTime -ge (Get-Item $dest).LastWriteTime) }
    if ($fresh) { $C.Add('| ' + $i + ' | ' + $rel + ' | FRESH |'); continue }
    Push-Location $OurRoot
    $text = ((& lake env lean $portRel 2>&1) | Out-String)
    $code = $LASTEXITCODE
    Pop-Location
    $errs = @()
    foreach ($ln in ($text -split $nl)) {
      if ($ln -match 'error' -and $errs.Count -lt $MaxErrorLines) {
        $s = $ln.Trim()
        if ($s.Length -gt 220) { $s = $s.Substring(0, 220) }
        $errs = $errs + $s
      }
    }
    if ($code -eq 0) { $C.Add('| ' + $i + ' | ' + $rel + ' | EXIT=0 |') }
    else { $C.Add('| ' + $i + ' | ' + $rel + ' | EXIT=' + $code + ' |'); $failed[$rel] = $true; $failedMsgs[$rel] = ($errs -join ' || ') }
  }
  $C.Add('')
  $C.Add('## Error digest')
  $C.Add('')
  if ($failedMsgs.Count -eq 0) { $C.Add('(no failures)') } else { foreach ($k in $failedMsgs.Keys) { $C.Add('- ' + $k + ': ' + $failedMsgs[$k]) } }
  Add-Content -LiteralPath (Join-Path $outRoot 'import_chain.md') -Value $nl -Value ($C -join $nl)
  Write-Output ('COMPILED files=' + $order.Count + ' failed=' + $failedMsgs.Count)
}

