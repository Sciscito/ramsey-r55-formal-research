param(
    [string]$PythonExecutable = 'python',
    [string]$LakeExecutable = 'lake',
    [switch]$AllowMissingGuardedProofBundle
)

$ErrorActionPreference = 'Stop'
$env:PYTHONDONTWRITEBYTECODE = '1'
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
    & $PythonExecutable -B -m unittest `
        test_catalog_certificate test_ramsey test_pilot_runner
    if ($LASTEXITCODE -ne 0) {
        throw 'Python tests failed.'
    }
    & $PythonExecutable -B catalog_certificate.py verify `
        . r35_extension_certificate.json
    if ($LASTEXITCODE -ne 0) {
        throw 'Catalogue certificate verification failed.'
    }
} finally {
    Pop-Location
}

Push-Location $repoRoot
try {
    & $PythonExecutable -B -m unittest discover `
        -s scripts\r45_d8_pilot -p 'test_gen4416_rooted*.py'
    if ($LASTEXITCODE -ne 0) {
        throw 'gen4416 rooted classifier tests failed.'
    }
    & $PythonExecutable -B scripts\r45_d8_pilot\gen358_lean_certificate.py verify
    if ($LASTEXITCODE -ne 0) {
        throw 'gen358 Lean certificate verification failed.'
    }
    & $PythonExecutable -B scripts\r45_d8_pilot\gen4416_rooted_classifier.py verify
    if ($LASTEXITCODE -ne 0) {
        throw 'gen4416 rooted classifier verification failed.'
    }
    & $PythonExecutable -B -m unittest `
        scripts.r45_d8_pilot.test_guarded_master `
        scripts.r45_d8_pilot.test_run_guarded_cover_lrat `
        scripts.r45_d8_pilot.test_proof_bundle
    if ($LASTEXITCODE -ne 0) {
        throw 'Guarded-master generator/runner tests failed.'
    }
    & $PythonExecutable -B scripts\r45_d8_pilot\generate_guarded_master.py verify
    if ($LASTEXITCODE -ne 0) {
        throw 'Guarded-master frozen artifact verification failed.'
    }
    & $PythonExecutable -B -m unittest `
        scripts.r45_d12_pilot.test_guarded_master `
        scripts.r45_d12_pilot.test_run_guarded_cover_lrat
    if ($LASTEXITCODE -ne 0) {
        throw 'Degree-twelve guarded-master generator/runner tests failed.'
    }
    & $PythonExecutable -B -m unittest discover `
        -s scripts\r45_d12_solver_strategy -p 'test_*.py'
    if ($LASTEXITCODE -ne 0) {
        throw 'Degree-twelve solver-strategy tests failed.'
    }
    & $PythonExecutable -B -m unittest discover `
        -s scripts\r45_d12_conditioned_cover -p 'test_*.py'
    if ($LASTEXITCODE -ne 0) {
        throw 'Degree-twelve conditioned-cover tests failed.'
    }
    & $PythonExecutable -B -m unittest discover `
        -s scripts\r45_d12_two_center_cover -p 'test_*.py'
    if ($LASTEXITCODE -ne 0) {
        throw 'Degree-twelve two-center-cover tests failed.'
    }
    & $PythonExecutable -B -m unittest discover `
        -s scripts\r45_d12_structural_cover -t . -p 'test_*.py'
    if ($LASTEXITCODE -ne 0) {
        throw 'Degree-twelve structural-cover tests failed.'
    }
    & $PythonExecutable -B -m unittest discover `
        -s scripts\r45_d12_gluing_aware_cover -t . -p 'test_*.py'
    if ($LASTEXITCODE -ne 0) {
        throw 'Degree-twelve gluing-aware-cover tests failed.'
    }
    $cover9UniversalTests = @(Get-ChildItem -LiteralPath (Join-Path $repoRoot 'scripts\r45_d12_cover9_universal') -File -Filter 'test_*.py' | Sort-Object Name | ForEach-Object {
            "scripts.r45_d12_cover9_universal.$($_.BaseName)"
        })
    & $PythonExecutable -B -m unittest @cover9UniversalTests
    if ($LASTEXITCODE -ne 0) {
        throw 'Degree-twelve cover9-universal tests failed.'
    }
    & $PythonExecutable -B -m unittest scripts.r45_d12_complement_closed_minimum.test_complement_closed_minimum
    if ($LASTEXITCODE -ne 0) {
        throw 'Complement-closed minimum tests failed.'
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
    & $PythonExecutable -B `
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
        LRATCatcher.Tests.R45DegreeEightGuardedMasterSemantics `
        LRATCatcher.Tests.R45RootDegreeCore `
        LRATCatcher.Tests.R45DegreeTwelveBridge `
        LRATCatcher.Tests.R45DegreeTwelveSelectorBridge `
        LRATCatcher.Tests.R45DegreeTwelveGlobalPermutation `
        LRATCatcher.Tests.R45DegreeTwelveCatalogueUnitsBridge `
        LRATCatcher.Tests.R45DegreeTwelvePartialBlueUnitsBridge `
        LRATCatcher.Tests.R45DegreeTwelveRawBlueBridge `
        LRATCatcher.Tests.R44OrderTwelveRootSymmetry `
        LRATCatcher.Tests.R44OrderTwelveRootSymmetryTransport `
        LRATCatcher.Tests.R44OrderTwelveDegreeBounds `
        LRATCatcher.Tests.R44OrderTwelveTwoCenterSymmetry `
        LRATCatcher.Tests.R44OrderTwelveTwoCenterCases `
        LRATCatcher.Tests.R44Cover6MotifBridge `
        LRATCatcher.Tests.R44Cover6CubeBridge `
        LRATCatcher.Tests.R44Cover6RepresentativeCubes `
        LRATCatcher.Tests.R44Cover6Master8CoreBridge `
        LRATCatcher.Tests.R44Cover6Master8IndexedSource `
        LRATCatcher.Tests.R44Cover6S7Transport `
        LRATCatcher.Tests.R44Cover6SemanticComposition `
        LRATCatcher.Tests.R44Cover6ConditionedWitnesses `
        LRATCatcher.Tests.R44Cover6DegreeSevenMinCenter `
        LRATCatcher.Tests.R44Cover6DegreeSevenNormalization `
        LRATCatcher.Tests.R44Cover6DegreeSevenR34Normalization `
        LRATCatcher.Tests.R44Cover6Master7R34IndexedSource `
        LRATCatcher.Tests.R44Cover6DegreeSevenR34Oracle `
        LRATCatcher.Tests.R44Cover6Master7R34FgraveGowCore `
        LRATCatcher.Tests.R44Cover6Master7R34FgraveGowSemantics `
        LRATCatcher.Tests.R44Cover6Master7R34FoDPOCore `
        LRATCatcher.Tests.R44Cover6Master7R34FoDPOSemantics `
        LRATCatcher.Tests.R44Cover6Master7R34FCUjCore `
        LRATCatcher.Tests.R44Cover6Master7R34FCUjSemantics `
        LRATCatcher.Tests.R44Cover6ToyChain `
        LRATCatcher.Tests.R55ExclusiveBlockR44
    if ($LASTEXITCODE -ne 0) {
        throw 'Lean integration build failed.'
    }
    $toyLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6ToyChain.lean 2>&1)
    $toyLeanExit = $LASTEXITCODE
    $toyLeanOutput | ForEach-Object { Write-Host $_ }
    if ($toyLeanExit -ne 0) {
        throw 'Cover6 toy forced Lean replay failed.'
    }
    Assert-AllowedLeanAxioms $toyLeanOutput `
        'Cover6 toy terminal theorem'
    $cover6MotifLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6MotifBridge.lean 2>&1)
    $cover6MotifLeanExit = $LASTEXITCODE
    $cover6MotifLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6MotifLeanExit -ne 0) {
        throw 'Cover6 motif bridge forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6MotifLeanOutput `
        'Cover6 motif blocker bridge'
    $cover6CubeLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6CubeBridge.lean 2>&1)
    $cover6CubeLeanExit = $LASTEXITCODE
    $cover6CubeLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6CubeLeanExit -ne 0) {
        throw 'Cover6 partial-cube bridge forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6CubeLeanOutput `
        'Cover6 partial-cube bridge'
    $cover6RepresentativeLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6RepresentativeCubes.lean 2>&1)
    $cover6RepresentativeLeanExit = $LASTEXITCODE
    $cover6RepresentativeLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6RepresentativeLeanExit -ne 0) {
        throw 'Cover6 representative-cube forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6RepresentativeLeanOutput `
        'Cover6 representative-cube certificate'
    $master8CoreBridgeLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6Master8CoreBridge.lean 2>&1)
    $master8CoreBridgeLeanExit = $LASTEXITCODE
    $master8CoreBridgeLeanOutput | ForEach-Object { Write-Host $_ }
    if ($master8CoreBridgeLeanExit -ne 0) {
        throw 'Master8 core-subset bridge forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $master8CoreBridgeLeanOutput `
        'Master8 core-subset bridge'
    $master8IndexedSourceLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6Master8IndexedSource.lean 2>&1)
    $master8IndexedSourceLeanExit = $LASTEXITCODE
    $master8IndexedSourceLeanOutput | ForEach-Object { Write-Host $_ }
    if ($master8IndexedSourceLeanExit -ne 0) {
        throw 'Master8 indexed-source forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $master8IndexedSourceLeanOutput `
        'Master8 indexed-source UNSAT bridge'
    $cover6S7LeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6S7Transport.lean 2>&1)
    $cover6S7LeanExit = $LASTEXITCODE
    $cover6S7LeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6S7LeanExit -ne 0) {
        throw 'Cover6 S7 transport forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6S7LeanOutput `
        'Cover6 S7 cube-to-motif transport'
    $cover6SemanticLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6SemanticComposition.lean 2>&1)
    $cover6SemanticLeanExit = $LASTEXITCODE
    $cover6SemanticLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6SemanticLeanExit -ne 0) {
        throw 'Cover6 semantic composition forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6SemanticLeanOutput `
        'Cover6 conditional semantic composition'
    $cover6ConditionedLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6ConditionedWitnesses.lean 2>&1)
    $cover6ConditionedLeanExit = $LASTEXITCODE
    $cover6ConditionedLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6ConditionedLeanExit -ne 0) {
        throw 'Cover6 conditioned-witness forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6ConditionedLeanOutput `
        'Cover6 degree-eight conditioned witness theorem'
    $cover6DegreeSevenLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6DegreeSevenMinCenter.lean 2>&1)
    $cover6DegreeSevenLeanExit = $LASTEXITCODE
    $cover6DegreeSevenLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6DegreeSevenLeanExit -ne 0) {
        throw 'Cover6 degree-seven minimum-centre forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6DegreeSevenLeanOutput `
        'Cover6 degree-seven minimum-centre theorem'
    $cover6DegreeSevenNormalizationLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6DegreeSevenNormalization.lean 2>&1)
    $cover6DegreeSevenNormalizationLeanExit = $LASTEXITCODE
    $cover6DegreeSevenNormalizationLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6DegreeSevenNormalizationLeanExit -ne 0) {
        throw 'Cover6 degree-seven normalization forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6DegreeSevenNormalizationLeanOutput `
        'Cover6 degree-seven exact nine-case normalization'
    $cover6DegreeSevenR34NormalizationLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6DegreeSevenR34Normalization.lean 2>&1)
    $cover6DegreeSevenR34NormalizationLeanExit = $LASTEXITCODE
    $cover6DegreeSevenR34NormalizationLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6DegreeSevenR34NormalizationLeanExit -ne 0) {
        throw 'Cover6 degree-seven R34 normalization forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6DegreeSevenR34NormalizationLeanOutput `
        'Cover6 degree-seven R34 catalogue normalization'
    $cover6Master7R34IndexedSourceLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6Master7R34IndexedSource.lean 2>&1)
    $cover6Master7R34IndexedSourceLeanExit = $LASTEXITCODE
    $cover6Master7R34IndexedSourceLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6Master7R34IndexedSourceLeanExit -ne 0) {
        throw 'Cover6 Master7 R34 indexed-source forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6Master7R34IndexedSourceLeanOutput `
        'Cover6 Master7 R34 indexed source'
    $cover6DegreeSevenR34OracleLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6DegreeSevenR34Oracle.lean 2>&1)
    $cover6DegreeSevenR34OracleLeanExit = $LASTEXITCODE
    $cover6DegreeSevenR34OracleLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6DegreeSevenR34OracleLeanExit -ne 0) {
        throw 'Cover6 degree-seven R34 oracle forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6DegreeSevenR34OracleLeanOutput `
        'Cover6 degree-seven direct R34 motif oracle'
    $cover6Master7FgraveGowLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6Master7R34FgraveGowCore.lean 2>&1)
    $cover6Master7FgraveGowLeanExit = $LASTEXITCODE
    $cover6Master7FgraveGowLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6Master7FgraveGowLeanExit -ne 0) {
        throw 'Cover6 Master7 F`GOW source/core bridge forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6Master7FgraveGowLeanOutput `
        'Cover6 Master7 F`GOW source/core UNSAT bridge'
    $cover6Master7FgraveGowSemanticsLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6Master7R34FgraveGowSemantics.lean 2>&1)
    $cover6Master7FgraveGowSemanticsLeanExit = $LASTEXITCODE
    $cover6Master7FgraveGowSemanticsLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6Master7FgraveGowSemanticsLeanExit -ne 0) {
        throw 'Cover6 Master7 F`GOW semantic closure forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6Master7FgraveGowSemanticsLeanOutput `
        'Cover6 Master7 F`GOW semantic leaf closure'
    $cover6Master7FoDPOLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6Master7R34FoDPOCore.lean 2>&1)
    $cover6Master7FoDPOLeanExit = $LASTEXITCODE
    $cover6Master7FoDPOLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6Master7FoDPOLeanExit -ne 0) {
        throw 'Cover6 Master7 FoDPO source/core bridge forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6Master7FoDPOLeanOutput `
        'Cover6 Master7 FoDPO source/core UNSAT bridge'
    $cover6Master7FoDPOSemanticsLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6Master7R34FoDPOSemantics.lean 2>&1)
    $cover6Master7FoDPOSemanticsLeanExit = $LASTEXITCODE
    $cover6Master7FoDPOSemanticsLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6Master7FoDPOSemanticsLeanExit -ne 0) {
        throw 'Cover6 Master7 FoDPO semantic closure forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6Master7FoDPOSemanticsLeanOutput `
        'Cover6 Master7 FoDPO semantic leaf closure'
    $cover6Master7FCUjLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6Master7R34FCUjCore.lean 2>&1)
    $cover6Master7FCUjLeanExit = $LASTEXITCODE
    $cover6Master7FCUjLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6Master7FCUjLeanExit -ne 0) {
        throw 'Cover6 Master7 FCUj source/core bridge forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6Master7FCUjLeanOutput `
        'Cover6 Master7 FCUj source/core UNSAT bridge'
    $cover6Master7FCUjSemanticsLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R44Cover6Master7R34FCUjSemantics.lean 2>&1)
    $cover6Master7FCUjSemanticsLeanExit = $LASTEXITCODE
    $cover6Master7FCUjSemanticsLeanOutput | ForEach-Object { Write-Host $_ }
    if ($cover6Master7FCUjSemanticsLeanExit -ne 0) {
        throw 'Cover6 Master7 FCUj semantic closure forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $cover6Master7FCUjSemanticsLeanOutput `
        'Cover6 Master7 FCUj semantic leaf closure'
    $master8CoreReplayLeanOutput = @(& $LakeExecutable env lean `
        ../../scripts/r45_d12_cover9_universal/master8_core/Replay.lean 2>&1)
    $master8CoreReplayLeanExit = $LASTEXITCODE
    $master8CoreReplayLeanOutput | ForEach-Object { Write-Host $_ }
    if ($master8CoreReplayLeanExit -ne 0) {
        throw 'Master8 reduced-core forced Lean replay failed.'
    }
    Assert-AllowedLeanAxioms $master8CoreReplayLeanOutput `
        'Master8 reduced-core dual replay'
    $master7FgraveGowCoreReplayLeanOutput = @(& $LakeExecutable env lean `
        ../../scripts/r45_d12_cover9_universal/master7_r34_fgravegow_core/Replay.lean 2>&1)
    $master7FgraveGowCoreReplayLeanExit = $LASTEXITCODE
    $master7FgraveGowCoreReplayLeanOutput | ForEach-Object { Write-Host $_ }
    if ($master7FgraveGowCoreReplayLeanExit -ne 0) {
        throw 'Master7 F`GOW reduced-core forced Lean replay failed.'
    }
    Assert-AllowedLeanAxioms $master7FgraveGowCoreReplayLeanOutput `
        'Master7 F`GOW reduced-core replay'
    $master7FoDPOCoreReplayLeanOutput = @(& $LakeExecutable env lean `
        ../../scripts/r45_d12_cover9_universal/master7_r34_fodpo_core/Replay.lean 2>&1)
    $master7FoDPOCoreReplayLeanExit = $LASTEXITCODE
    $master7FoDPOCoreReplayLeanOutput | ForEach-Object { Write-Host $_ }
    if ($master7FoDPOCoreReplayLeanExit -ne 0) {
        throw 'Master7 FoDPO reduced-core forced Lean replay failed.'
    }
    Assert-AllowedLeanAxioms $master7FoDPOCoreReplayLeanOutput `
        'Master7 FoDPO reduced-core replay'
    $master7FCUjCoreReplayLeanOutput = @(& $LakeExecutable env lean `
        ../../scripts/r45_d12_cover9_universal/master7_r34_fcuj_core/Replay.lean 2>&1)
    $master7FCUjCoreReplayLeanExit = $LASTEXITCODE
    $master7FCUjCoreReplayLeanOutput | ForEach-Object { Write-Host $_ }
    if ($master7FCUjCoreReplayLeanExit -ne 0) {
        throw 'Master7 FCUj reduced-core forced Lean replay failed.'
    }
    Assert-AllowedLeanAxioms $master7FCUjCoreReplayLeanOutput `
        'Master7 FCUj reduced-core replay'
    $exclusiveBlockLeanOutput = @(& $LakeExecutable env lean `
        LRATCatcher/Tests/R55ExclusiveBlockR44.lean 2>&1)
    $exclusiveBlockLeanExit = $LASTEXITCODE
    $exclusiveBlockLeanOutput | ForEach-Object { Write-Host $_ }
    if ($exclusiveBlockLeanExit -ne 0) {
        throw 'Exclusive-block forced Lean check failed.'
    }
    Assert-AllowedLeanAxioms $exclusiveBlockLeanOutput `
        'Exclusive-block R44 theorem'
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
