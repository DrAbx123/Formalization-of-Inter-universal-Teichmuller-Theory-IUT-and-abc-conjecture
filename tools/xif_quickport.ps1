<#
.SYNOPSIS
  Ad-hoc single-target porting helper: port any Lean file(s) from a cloned external repo into
  this workspace, then feed dependency-ready files to the watchdog queue. Use freely during work.
.DESCRIPTION
  Repo aliases: flt (tmp/external/flt-lean), tauceti (tmp/TauCeti),
                cft (tmp/external/ClassFieldTheory), tauceti-main (tmp/external/tauceti-extract/TauCeti-main),
                flt-p2m (tmp/external/flt-lean), mathlib-newsrc (tmp/external/mathlib-new, if cloned).
  Each call ports the import closure of -File (relative to repo root, e.g. TauCeti/FieldTheory/FunctionField/RiemannRoch/Basic.lean),
  writes it under tmp/external/ported/<Name>, then runs xif_port_feeder.ps1 for that dir.
.EXAMPLE
  tools/xif_quickport.ps1 -Repo tauceti -File TauCeti/FieldTheory/FunctionField/Belyi/Existence.lean -Name tauceti_adhoc
#>
param(
  [Parameter(Mandatory=$true)][string]$Repo,
  [Parameter(Mandatory=$true)][string[]]$File,
  [string]$Name = '',
  [int]$Feed = 24,
  [switch]$NoFeed
)
$ErrorActionPreference = 'Continue'
$root = 'D:\lean'
$aliases = @{
  'flt' = (Join-Path $root 'tmp\external\flt-lean')
  'tauceti' = (Join-Path $root 'tmp\TauCeti')
  'tauceti-main' = (Join-Path $root 'tmp\external\tauceti-extract\TauCeti-main')
  'cft' = (Join-Path $root 'tmp\external\ClassFieldTheory')
  'compelliptic' = (Join-Path $root 'tmp\external\CompElliptic')
}
if (-not $aliases.ContainsKey($Repo)) { Write-Output ('UNKNOWN REPO ' + $Repo + ' ; aliases: ' + (($aliases.Keys | Sort-Object) -join ', ')); exit 1 }
$src = $aliases[$Repo]
if (-not (Test-Path $src)) { Write-Output ('SRC MISSING ' + $src); exit 1 }
if ($Name -eq '') { $Name = 'adhoc_' + $Repo }
$files = @($File | ForEach-Object { $_ -split '[,;]' } | ForEach-Object { $_.Trim() } | Where-Object { $_.Length -gt 0 })
$targets = ($files -join ';')
$port = Join-Path $root 'tools\xif_external_port.ps1'
$feeder = Join-Path $root 'tools\xif_port_feeder.ps1'
Write-Output ('=== quickport repo=' + $Repo + ' name=' + $Name + ' files=' + $files.Count + ' ===')
& 'C:\Program Files\PowerShell\7\pwsh.exe' -NoProfile -File $port -Name $Name -SrcRoot $src -Targets $targets -Port 2>&1 | Select-Object -Last 3
$dir = Join-Path $root ('tmp\external\ported\' + $Name)
if (Test-Path $dir) {
  Write-Output ('ported dir=' + $dir)
  if (-not $NoFeed) {
    & 'C:\Program Files\PowerShell\7\pwsh.exe' -NoProfile -File $feeder -Dir $dir -MaxAdd $Feed 2>&1 | Select-Object -Last 3
  }
  Write-Output ('next: after compile green, import tmp.external.ported.' + $Name + '.<ModulePath>')
} else { Write-Output 'PORT FAILED (no dir)' }
