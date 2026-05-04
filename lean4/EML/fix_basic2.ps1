$f = "Basic.lean"
$c = [IO.File]::ReadAllText($f, [Text.Encoding]::UTF8)

$fixes = @(
  @('Resultado: 1 - \.\.\. — ESPERA: la definici.n de tMinus es app \(tLog one\) \(tExp t\),',
    'Result: 1 - ... — NOTE: the definition of tMinus is app (tLog one) (tExp t),'),
  @('as. \u27e6tMinus t\u27e7\(z\) = exp\(\u27e6tLog one\u27e7\(z\)\) - log\(\u27e6tExp t\u27e7\(z\)\)',
    'so \u27e6tMinus t\u27e7(z) = exp(\u27e6tLog one\u27e7(z)) - log(\u27e6tExp t\u27e7(z))'),
  @('de depth creciente\.', 'of increasing depth.'),
  @('§11\. INDUCCI.N ESTRUCTURAL SOBRE EMLTerm', '§11. STRUCTURAL INDUCTION ON EMLTerm'),
  @('§12\. N.MEROS DE CATALAN Y LA GRA.TICA EML', '§12. CATALAN NUMBERS AND THE EML GRAMMAR'),
  @('Para n=1: 1 .rbol \(one\)', 'For n=1: 1 tree (one)'),
  @('Para n=2: 1 .rbol \(app one one\)', 'For n=2: 1 tree (app one one)'),
  @('Para n=3: 2 .rboles', 'For n=3: 2 trees'),
  @('Para n=4: 5 .rboles', 'For n=4: 5 trees')
)

foreach ($fix in $fixes) {
  $c = $c -replace $fix[0], $fix[1]
}

[IO.File]::WriteAllText($f, $c, [Text.Encoding]::UTF8)
Write-Host "Done."
$hits = Select-String -Path $f -Pattern "^\s*--.*[áéíóúñü]"
if ($hits) { $hits | Select-Object LineNumber,Line } else { Write-Host "No Spanish comments remaining." }
