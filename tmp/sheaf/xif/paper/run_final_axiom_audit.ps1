param(
  [string]$Repo = "D:\lean",
  [string]$AuditDir = "D:\lean\tmp\sheaf\xif\paper"
)

$ErrorActionPreference = "Stop"

$targetsFile = Join-Path $AuditDir "FinalAuditTargets.txt"
$importsFile = Join-Path $AuditDir "FinalAuditImports.txt"
$filesFile   = Join-Path $AuditDir "FinalAuditFiles.txt"
$probeFile   = Join-Path $AuditDir "FinalAxiomProbe.generated.lean"
$outputFile  = Join-Path $AuditDir "FinalAxiomAudit.generated.log"

$targets = Get-Content $targetsFile |
  Where-Object { $_.Trim() -ne "" -and -not $_.Trim().StartsWith("#") } |
  ForEach-Object { $_.Trim() }
$imports = Get-Content $importsFile |
  Where-Object { $_.Trim() -ne "" -and -not $_.Trim().StartsWith("#") } |
  ForEach-Object { $_.Trim() }

$lines = @()
foreach ($imp in $imports) { $lines += "import " + $imp }
$lines += ""
foreach ($t in $targets) {
  $lines += "#print axioms " + $t
  $lines += ""
}
Set-Content -Path $probeFile -Value $lines -Encoding UTF8

Push-Location $Repo
try {
  $out = & lake env lean -j1 -R $Repo $probeFile 2>&1 | Out-String
  $exitCode = $LASTEXITCODE
} finally {
  Pop-Location
}
Set-Content -Path $outputFile -Value $out -Encoding UTF8

Write-Output ("LEAN EXIT=" + $exitCode)
Write-Output ("AXIOM LOG=" + $outputFile)

$fail = @()
if ($exitCode -ne 0) { $fail += "Lean exited nonzero: $exitCode" }
if ($out -match "unknown constant|unknown declaration|object file .* does not exist") {
  $fail += "Missing module/declaration in probe"
}
if ($out -match "sorryAx") { $fail += "sorryAx present in axiom output" }

$allowed = @("propext", "Classical.choice", "Quot.sound")
$axiomSets = @()
$matches = [regex]::Matches($out, "depends on axioms:\s*\[([^\]]*)\]")
if ($matches.Count -eq 0) {
  $matches = [regex]::Matches($out, ":\s*\[([^\]]*)\]")
}
foreach ($m in $matches) {
  $set = $m.Groups[1].Value.Split(",") | ForEach-Object { $_.Trim() } | Where-Object { $_ -ne "" }
  $axiomSets += ,$set
  foreach ($a in $set) {
    if ($allowed -notcontains $a) { $fail += "Disallowed axiom: $a" }
  }
}
if ($axiomSets.Count -eq 0) { $fail += "No #print axioms output parsed" }

$sourceHits = @()
if (Test-Path $filesFile) {
  $auditFiles = Get-Content $filesFile |
    Where-Object { $_.Trim() -ne "" -and -not $_.Trim().StartsWith("#") } |
    ForEach-Object { $_.Trim().Replace("/", "\") }
  foreach ($rel in $auditFiles) {
    $full = Join-Path $Repo $rel
    if (Test-Path $full) {
      $hits = Select-String -Path $full -Pattern "\bsorry\b|\badmit\b|^\s*axiom\b" -AllMatches
      foreach ($h in $hits) {
        $sourceHits += ("$rel" + ":" + $h.LineNumber + ":" + $h.Line.Trim())
      }
    } else {
      $sourceHits += "MISSING FILE: $rel"
    }
  }
}
if ($sourceHits.Count -gt 0) {
  Write-Output "SOURCE REVIEW HITS (comments may be benign; sorryAx is authoritative):"
  $sourceHits | ForEach-Object { Write-Output $_ }
  foreach ($hit in $sourceHits) {
    if ($hit.StartsWith("MISSING FILE:")) { $fail += $hit }
  }
}

Write-Output "AXIOM SETS:"
foreach ($set in $axiomSets) { Write-Output ("  [" + ($set -join ", ") + "]") }

if ($fail.Count -gt 0) {
  Write-Output "AXIOM AUDIT FAIL"
  $fail | ForEach-Object { Write-Output ("  - " + $_) }
  exit 1
}

Write-Output "AXIOM AUDIT PASS"
Write-Output "Axioms: propext Classical.choice Quot.sound"
exit 0
