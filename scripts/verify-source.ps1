param(
    [string]$PythonExecutable = 'python',
    [string]$LakeExecutable = 'lake',
    [switch]$AllowMissingGuardedProofBundle
)

$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path -Parent $PSScriptRoot

function Assert-AllowedLeanAxioms {
    param(
        [object[]]$LeanOutput,
        [string]$Label
    )
    $joined = $LeanOutput -join "`n"
    if ($joined -match '\bsorryAx\b') {
        throw "$Label depends on sorryAx."
    }
    $reports = [regex]::Matches(
        $joined,
        'depends on axioms:\s*\[(.*?)\]',
        [Text.RegularExpressions.RegexOptions]::Singleline
    )
    if ($reports.Count -eq 0) {
        throw "$Label emitted no parseable #print axioms report."
    }
    foreach ($report in $reports) {
        foreach ($rawName in $report.Groups[1].Value.Split(',')) {
            $name = $rawName.Trim().TrimEnd([char]0x271D)
            $allowedStandard = $name -in @(
                'propext',
                'Classical.choice',
                'Quot.sound'
            )
            $allowedNative =
                $name -match '^.+\._native\.native_decide\.ax_[0-9]+_[0-9]+$'
            if (-not $allowedStandard -and -not $allowedNative) {
                throw "$Label has unexpected axiom: $name"
            }
        }
    }
}

$proofArtifacts = @(
    @{
        Path = Join-Path $repoRoot `
            'scripts\r45_d8_pilot\evidence\lrat\d8_l22_r01.cnf'
        Sha256 = 'F2E1D012DEA5911F9F4D9F7B50641CA483ECE5F65B1F666E92BE61CF332AFEAF'
    },
    @{
        Path = Join-Path $repoRoot `
            'scripts\r45_d8_pilot\evidence\lrat\d8_l22_r01.lrat'
        Sha256 = '3EB38EFAEBDDE8E4B2EF0FD78B1AC5C6B449FC8E1A1D814A94511081290E9023'
    }
)
foreach ($artifact in $proofArtifacts) {
    if (-not (Test-Path -LiteralPath $artifact.Path)) {
        throw "Missing proof artifact: $($artifact.Path)"
    }
    $actualHash = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath $artifact.Path).Hash
    if ($actualHash -ne $artifact.Sha256) {
        throw "Proof artifact hash mismatch: $($artifact.Path)"
    }
}

Push-Location (Join-Path $repoRoot 'r55')
try {
    & $PythonExecutable -m unittest `
        test_catalog_certificate test_ramsey test_pilot_runner
    if ($LASTEXITCODE -ne 0) {
        throw 'Python tests failed.'
    }
    & $PythonExecutable catalog_certificate.py verify `
        . r35_extension_certificate.json
    if ($LASTEXITCODE -ne 0) {
        throw 'Catalogue certificate verification failed.'
    }
} finally {
    Pop-Location
}

Push-Location $repoRoot
try {
    & $PythonExecutable -m unittest discover `
        -s scripts\r45_d8_pilot -p 'test_gen4416_rooted*.py'
    if ($LASTEXITCODE -ne 0) {
        throw 'gen4416 rooted classifier tests failed.'
    }
    & $PythonExecutable scripts\r45_d8_pilot\gen358_lean_certificate.py verify
    if ($LASTEXITCODE -ne 0) {
        throw 'gen358 Lean certificate verification failed.'
    }
    & $PythonExecutable scripts\r45_d8_pilot\gen4416_rooted_classifier.py verify
    if ($LASTEXITCODE -ne 0) {
        throw 'gen4416 rooted classifier verification failed.'
    }
    & $PythonExecutable -m unittest `
        scripts.r45_d8_pilot.test_guarded_master `
        scripts.r45_d8_pilot.test_run_guarded_cover_lrat `
        scripts.r45_d8_pilot.test_proof_bundle
    if ($LASTEXITCODE -ne 0) {
        throw 'Guarded-master generator/runner tests failed.'
    }
    & $PythonExecutable scripts\r45_d8_pilot\generate_guarded_master.py verify
    if ($LASTEXITCODE -ne 0) {
        throw 'Guarded-master frozen artifact verification failed.'
    }
} finally {
    Pop-Location
}

$guardedMasterDirectory = Join-Path $repoRoot `
    'scripts\r45_d8_pilot\guarded_master'
$proofBundleDirectory = Join-Path $guardedMasterDirectory 'proofs'
$proofManifestPath = Join-Path $guardedMasterDirectory `
    'proof_bundle_manifest.json'
$proofManifest = Get-Content -LiteralPath $proofManifestPath -Raw |
    ConvertFrom-Json
$expectedProofNames = @($proofManifest.files | ForEach-Object { $_.name })
if ($expectedProofNames.Count -ne 60 -or
    (@($expectedProofNames | Sort-Object -Unique)).Count -ne 60) {
    throw 'Guarded-master proof manifest does not list 60 unique files.'
}
$presentProofNames = @()
if (Test-Path -LiteralPath $proofBundleDirectory) {
    $presentProofNames = @(Get-ChildItem -LiteralPath $proofBundleDirectory `
        -File -Filter '*.lrat' | ForEach-Object { $_.Name })
}
$unexpectedProofNames = @($presentProofNames |
    Where-Object { $_ -notin $expectedProofNames })
if ($unexpectedProofNames.Count -gt 0) {
    throw "Unexpected guarded-master LRATs: $($unexpectedProofNames -join ', ')"
}
$missingProofNames = @($expectedProofNames |
    Where-Object { $_ -notin $presentProofNames })
if ($presentProofNames.Count -gt 0 -and $missingProofNames.Count -gt 0) {
    throw "Guarded-master proof bundle is partial; missing: $($missingProofNames -join ', ')"
}
$hasGuardedProofBundle = $missingProofNames.Count -eq 0
if (-not $hasGuardedProofBundle -and -not $AllowMissingGuardedProofBundle) {
    throw 'Guarded-master proof bundle is absent. Install it with proof_bundle.py, or pass -AllowMissingGuardedProofBundle for a non-publication smoke test.'
}
if ($hasGuardedProofBundle) {
    & $PythonExecutable `
        (Join-Path $repoRoot 'scripts\r45_d8_pilot\run_guarded_cover_lrat.py') `
        --output $proofBundleDirectory --verify-bundle
    if ($LASTEXITCODE -ne 0) {
        throw 'Guarded-master proof-bundle verification failed.'
    }
} else {
    Write-Warning 'Guarded-master LRAT bundle absent by explicit opt-out; terminal replay will be skipped.'
}

Push-Location (Join-Path $repoRoot 'vendor\lrat-catcher')
try {
    & $LakeExecutable build `
        LRATCatcher.CoverTrim `
        LRATCatcher.Tests.ReflectTest `
        lratcatch-cover-parallel-trim `
        LRATCatcher.Tests.R35CatalogCheckpoint `
        LRATCatcher.Tests.R55W5Symmetry `
        LRATCatcher.Tests.R55CommonNeighborhoodBridge `
        LRATCatcher.Tests.R55CanonicalUnitsBridge `
        LRATCatcher.Tests.R55TypedUnitsBridge `
        LRATCatcher.Tests.R55CanonicalCommonIndex `
        LRATCatcher.Tests.R55ColoringPermutation `
        LRATCatcher.Tests.R55CanonicalRelabeling `
        LRATCatcher.Tests.RamseyUpperBounds `
        LRATCatcher.Tests.R55DegreeBounds `
        LRATCatcher.Tests.R44RootedR34Catalogue `
        LRATCatcher.Tests.R44RootedGen4416Classifier `
        LRATCatcher.Tests.R44RootedGraphReduction `
        LRATCatcher.Tests.R44RootedDegreeSplit `
        LRATCatcher.Tests.R44RootedBlockCatalogues `
        LRATCatcher.Tests.R44RootedGen4416Semantics `
        LRATCatcher.Tests.R44RootedMixedClauses `
        LRATCatcher.Tests.R44RootedMixedCNFSemantics `
        LRATCatcher.Tests.R44RootedCanonicalRelabeling `
        LRATCatcher.Tests.R44RootedGen4416CoverData `
        LRATCatcher.Tests.R44RootedGen4416Cover `
        LRATCatcher.Tests.R44Gen4416TargetAudit `
        LRATCatcher.Tests.R44Gen4416Classification `
        LRATCatcher.Tests.R45DegreeEightCover `
        LRATCatcher.Tests.R45DegreeEightBridge `
        LRATCatcher.Tests.R45DegreeEightGen4416Bridge `
        LRATCatcher.Tests.R45DegreeEightGlobalPermutation `
        LRATCatcher.Tests.R45DegreeEightRawGen4416Bridge `
        LRATCatcher.Tests.R45DegreeEightGen358UnitsBridge `
        LRATCatcher.Tests.R45DegreeEightGen4416UnitsBridge `
        LRATCatcher.Tests.R45DegreeEightLeafAssemblyCore `
        LRATCatcher.Tests.R45DegreeEightPilot `
        LRATCatcher.Tests.R45DegreeEightPilotSemantics `
        LRATCatcher.Tests.R45DegreeEightReducedAssignment `
        LRATCatcher.Tests.R45DegreeEightPilotAssembly `
        LRATCatcher.Tests.R45DegreeEightBranchComposition `
        LRATCatcher.Tests.R45DegreeEightGuardedMasterSemantics
    if ($LASTEXITCODE -ne 0) {
        throw 'Lean integration build failed.'
    }
    if ($hasGuardedProofBundle) {
        $guardedLeanOutput = @(& $LakeExecutable env lean `
            LRATCatcher/Tests/R45DegreeEightGuardedMaster.lean 2>&1)
        $guardedLeanExit = $LASTEXITCODE
        $guardedLeanOutput | ForEach-Object { Write-Host $_ }
        if ($guardedLeanExit -ne 0) {
            throw 'Guarded-master forced Lean replay failed.'
        }
        Assert-AllowedLeanAxioms $guardedLeanOutput `
            'Guarded-master terminal theorem'
        $remainingLeanOutput = @(& $LakeExecutable env lean `
            LRATCatcher/Tests/R45RemainingDegrees.lean 2>&1)
        $remainingLeanExit = $LASTEXITCODE
        $remainingLeanOutput | ForEach-Object { Write-Host $_ }
        if ($remainingLeanExit -ne 0) {
            throw 'Remaining-degree forced Lean replay failed.'
        }
        Assert-AllowedLeanAxioms $remainingLeanOutput `
            'Remaining-degree consequence'
    }
} finally {
    Pop-Location
}

if ($hasGuardedProofBundle) {
    Write-Host 'Full source and external-proof verification completed successfully.' `
        -ForegroundColor Green
} else {
    Write-Warning 'Source-only smoke test completed; external terminal theorem was not replayed.'
}
