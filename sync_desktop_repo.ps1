param(
    [string]$RepoUrl = "https://github.com/Lynamator123/RockyIdleReader.git",
    [string]$TargetPath = "$env:USERPROFILE\Desktop\Rocky Idle Reader"
)

$gitCmd = Get-Command git -ErrorAction SilentlyContinue
if (-not $gitCmd) {
    Write-Host "Git is not installed or not on PATH. Install Git first, then rerun this script." -ForegroundColor Red
    exit 1
}

if (-not (Test-Path $TargetPath)) {
    New-Item -ItemType Directory -Path $TargetPath -Force | Out-Null
}

$gitFolder = Join-Path $TargetPath ".git"
if (-not (Test-Path $gitFolder)) {
    Write-Host "Cloning repository into: $TargetPath" -ForegroundColor Cyan
    git clone $RepoUrl $TargetPath
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
} else {
    Write-Host "Pulling latest changes in: $TargetPath" -ForegroundColor Cyan
    Push-Location $TargetPath
    try {
        git fetch origin
        if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
        git pull --ff-only origin main
        if ($LASTEXITCODE -ne 0) {
            Write-Host "Fast-forward pull failed. Resolve local changes manually." -ForegroundColor Yellow
            exit $LASTEXITCODE
        }
    }
    finally {
        Pop-Location
    }
}

Write-Host "Desktop repo is up to date." -ForegroundColor Green
