param(
    [string]$RepoUrl = "https://github.com/Lynamator123/RockyIdleReader.git",
    [string]$Branch = "main",
    [string]$CommitMessage = "Initial import from local workspace"
)

$gitCmd = Get-Command git -ErrorAction SilentlyContinue
if (-not $gitCmd) {
    Write-Host "Git is not installed or not on PATH. Install Git first, then rerun this script." -ForegroundColor Red
    exit 1
}

if (-not (Test-Path ".git")) {
    git init
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}

git add .
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

git commit -m $CommitMessage
if ($LASTEXITCODE -ne 0) {
    Write-Host "Commit failed (possibly no changes). Continuing..." -ForegroundColor Yellow
}

$existingRemote = git remote
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
if ($existingRemote -notcontains "origin") {
    git remote add origin $RepoUrl
} else {
    git remote set-url origin $RepoUrl
}
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

git branch -M $Branch
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

git push -u origin $Branch
exit $LASTEXITCODE
