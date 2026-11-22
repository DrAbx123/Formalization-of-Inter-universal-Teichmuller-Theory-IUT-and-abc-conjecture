# Resource-aware build admission v4 (2026-10-17): stagger starts using actual pressure.
# Keep shared v2 gate/stamp and v3 semaphore names for existing launchers.
param(
  [Parameter(Mandatory=$true, Position=0)][string]$Command,
  [string]$Log = '',
  [ValidateRange(1,1024)][int]$Slots = 12,
  [ValidateRange(0,1048576)][double]$MinFreeGB = 4,
  [ValidateRange(1,100)][int]$MaxCPU = 80,
  [ValidateRange(0,3600)][double]$ColdGapSec = 5,
  [ValidateRange(0,1048576)][double]$MinCommitHeadGB = 3,
  [ValidateRange(0,1048576)][double]$StartupReserveGB = 2,
  [ValidateRange(0,3600)][double]$GrowthHorizonSec = 5,
  [ValidateRange(0.1,3600)][double]$PollSec = 2,
  [ValidateRange(1,86400)][int]$WaitTimeoutSec = 7200,
  [string]$WorkDir = 'D:\lean'
)
# 2026-10-18: this host has no pagefile (commit limit == 32 GB RAM); with ~9 GB
# headroom the old 8+3 floors blocked every build forever. Floors lowered to 3+2.
$ErrorActionPreference = 'Stop'
$tag = ([guid]::NewGuid().ToString('N')).Substring(0,8)
$stampDir = 'D:\lean\tmp\build-guard-logs'
[void][System.IO.Directory]::CreateDirectory($stampDir)
if (-not $Log) { $Log = Join-Path $stampDir (((Get-Date).ToString('yyyyMMdd-HHmmss')) + "-$tag.log") }
$logDir = Split-Path -Parent $Log
if ($logDir) { [void][System.IO.Directory]::CreateDirectory($logDir) }
$launchStamp = Join-Path $stampDir '.last-launch'
function Write-G {
  param([string]$Message)
  $line = (Get-Date).ToString('HH:mm:ss') + " [$tag] " + $Message
  Add-Content -LiteralPath $Log -Value $line
  Write-Output $line
}
function Get-ResourceSnapshot {
  $os = Get-CimInstance Win32_OperatingSystem
  $memory = Get-CimInstance Win32_PerfFormattedData_PerfOS_Memory
  $cpu = (Get-CimInstance Win32_Processor | Measure-Object LoadPercentage -Average).Average
  if ($null -eq $cpu -or $null -eq $os.FreePhysicalMemory -or
      $null -eq $memory.CommitLimit -or $null -eq $memory.CommittedBytes) {
    throw 'Incomplete resource counters'
  }
  [pscustomobject]@{
    Time = [System.Diagnostics.Stopwatch]::GetTimestamp() / [double][System.Diagnostics.Stopwatch]::Frequency
    CPU = [double]$cpu
    FreeGB = [double]$os.FreePhysicalMemory / 1MB
    CommitHeadGB = ([double]$memory.CommitLimit - [double]$memory.CommittedBytes) / 1GB
  }
}
# Pure admission rule. Round only displays, never resource decisions.
# Reserve room for a new start and projected growth of already running work.
function Get-AdmissionDecision {
  param($Current, $Previous, [double]$FreeFloor, [double]$CommitFloor,
        [double]$Reserve, [double]$Horizon, [double]$CpuLimit)
  $growth = 0.0
  if ($null -ne $Previous) {
    $elapsed = $Current.Time - $Previous.Time
    if ($elapsed -gt 0) {
      $growth = [math]::Max(0, [math]::Max(
        $Previous.FreeGB - $Current.FreeGB,
        $Previous.CommitHeadGB - $Current.CommitHeadGB)) / $elapsed * $Horizon
    }
  }
  $requiredFree = $FreeFloor + $Reserve + $growth
  $requiredCommit = $CommitFloor + $Reserve + $growth
  $reason = if ($Current.CPU -ge $CpuLimit) { 'high-cpu' }
    elseif ($Current.FreeGB -lt $requiredFree) { 'physical-memory' }
    elseif ($Current.CommitHeadGB -lt $requiredCommit) { 'commit-headroom' }
    else { 'ready' }
  [pscustomobject]@{
    Ready = $reason -eq 'ready'; Reason = $reason
    GrowthGB = $growth; RequiredFreeGB = $requiredFree; RequiredCommitGB = $requiredCommit
  }
}
function Get-LaunchGapSeconds {
  if (-not (Test-Path -LiteralPath $launchStamp)) { return 0.0 }
  $last = [datetimeoffset]::Parse((Get-Content -LiteralPath $launchStamp -Raw).Trim())
  return [math]::Max(0, $ColdGapSec - ([datetimeoffset]::Now - $last).TotalSeconds)
}
Write-G "guard v4 start fuse=$Slots maxCPU=$MaxCPU minFreeGB=$MinFreeGB minCommitHeadGB=$MinCommitHeadGB reserveGB=$StartupReserveGB growthHorizon=$GrowthHorizonSec coldGap=$ColdGapSec poll=$PollSec"
Write-G "cmd=$Command"
$sem = $null; $gate = $null; $slotHeld = $false; $child = $null
$outFile = $Log + '.stdout.tmp'; $errFile = $Log + '.stderr.tmp'
$timer = [System.Diagnostics.Stopwatch]::StartNew()
$previous = $null; $consecutive = 0; $lastReason = ''; $lastReport = -30.0
try {
  try { $sem = [System.Threading.Semaphore]::new($Slots, $Slots, 'Global\lean_build_guard_slots_v3') }
  catch { $sem = [System.Threading.Semaphore]::new($Slots, $Slots, 'lean_build_guard_slots_v3') }
  try { $gate = [System.Threading.Mutex]::new($false, 'Global\lean_build_guard_gate_v2') }
  catch { $gate = [System.Threading.Mutex]::new($false, 'lean_build_guard_gate_v2') }
  Write-G "waiting for fuse slot (timeout ${WaitTimeoutSec}s)"
  if (-not $sem.WaitOne([TimeSpan]::FromSeconds($WaitTimeoutSec))) { Write-G 'TIMEOUT waiting for fuse slot'; exit 2 }
  $slotHeld = $true
  Write-G 'fuse slot acquired'
  while ($true) {
    if ($timer.Elapsed.TotalSeconds -ge $WaitTimeoutSec) { Write-G 'TIMEOUT waiting for resources'; exit 2 }
    $reason = 'sampling'; $detail = ''; $delay = $PollSec
    try {
      # Ordinary samples do not hold the shared gate.
      $current = Get-ResourceSnapshot
      $decision = Get-AdmissionDecision $current $previous $MinFreeGB $MinCommitHeadGB $StartupReserveGB $GrowthHorizonSec $MaxCPU
      if ($decision.Ready) { $consecutive++ } else { $consecutive = 0 }
      $reason = $decision.Reason
      $detail = 'cpu={0:0.#}% freeGB={1:0.00} commitHead={2:0.00} projectedGrowthGB={3:0.00}' -f $current.CPU,$current.FreeGB,$current.CommitHeadGB,$decision.GrowthGB
      if ($consecutive -ge 2) {
        $gateOK = $false
        try { $gateOK = $gate.WaitOne([TimeSpan]::FromSeconds(1)) }
        catch [System.Threading.AbandonedMutexException] { $gateOK = $true }
        if ($gateOK) {
          try {
            $gap = Get-LaunchGapSeconds
            if ($gap -gt 0) {
              $reason = 'launch-gap'
              $delay = [math]::Min($PollSec, [math]::Max(0.1, $gap))
            } else {
              # Fresh check and start are atomic. Never sleep inside the gate.
              $fresh = Get-ResourceSnapshot
              $instant = Get-AdmissionDecision $fresh $previous $MinFreeGB $MinCommitHeadGB $StartupReserveGB $GrowthHorizonSec $MaxCPU
              if ($instant.Ready -and $timer.Elapsed.TotalSeconds -lt $WaitTimeoutSec) {
                Write-G ('launching: cpu={0:0.#}% freeGB={1:0.00} commitHead={2:0.00} projectedGrowthGB={3:0.00}' -f $fresh.CPU,$fresh.FreeGB,$fresh.CommitHeadGB,$instant.GrowthGB)
                $wrapped = '$ErrorActionPreference = ''Stop''; $LASTEXITCODE = 0; try {' + "`n" + $Command + "`n" + '; exit $LASTEXITCODE } catch { [Console]::Error.WriteLine($_); exit 1 }'
                $encoded = [Convert]::ToBase64String([Text.Encoding]::Unicode.GetBytes($wrapped))
                $child = Start-Process -FilePath 'pwsh' -ArgumentList @('-NoProfile','-EncodedCommand',$encoded) -WorkingDirectory $WorkDir -RedirectStandardOutput $outFile -RedirectStandardError $errFile -PassThru -WindowStyle Hidden
                Set-Content -LiteralPath $launchStamp -Value ([datetimeoffset]::Now.ToString('o'))
                Write-G "launched pid=$($child.Id)"
              } else { $reason = $instant.Reason; $consecutive = 0 }
            }
          } finally { $gate.ReleaseMutex() }
        } else { $reason = 'gate-busy' }
      }
      $previous = $current
    } catch {
      if ($child) { throw }
      $reason = 'sample-error'; $detail = $_.Exception.Message
      $consecutive = 0; $previous = $null
    }
    if ($child) { break }
    if ($reason -ne $lastReason -or $timer.Elapsed.TotalSeconds - $lastReport -ge 15) {
      Write-G "waiting($reason): $detail"
      $lastReason = $reason; $lastReport = $timer.Elapsed.TotalSeconds
    }
    Start-Sleep -Milliseconds ([int]($delay * 1000))
  }
  $child.WaitForExit()
  $code = $child.ExitCode
  if (Test-Path -LiteralPath $outFile) {
    Add-Content -LiteralPath $Log -Value "----- build stdout -----`n$(Get-Content -LiteralPath $outFile -Raw)"
    Remove-Item -LiteralPath $outFile -Force
  }
  if (Test-Path -LiteralPath $errFile) {
    $stderr = Get-Content -LiteralPath $errFile -Raw
    if ($stderr) { Add-Content -LiteralPath $Log -Value "----- build stderr -----`n$stderr" }
    Remove-Item -LiteralPath $errFile -Force
  }
  Write-G "cmd exit=$code total=$([math]::Round($timer.Elapsed.TotalSeconds,1))s log=$Log"
  exit $code
} finally {
  if ($slotHeld) { [void]$sem.Release() }
  if ($sem) { $sem.Dispose() }
  if ($gate) { $gate.Dispose() }
}

