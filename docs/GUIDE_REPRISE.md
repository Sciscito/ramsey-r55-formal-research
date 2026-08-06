# Guide de reprise du projet R(5,5)

État figé le 6 août 2026, fuseau Europe/Paris.

Ce document accompagne l’archive `R55_REPRISE_COMPLET_2026-08-06.zip`.
L’archive complète est la sauvegarde à conserver lors du changement de PC.

## 1. Ce qui est démontré — et ce qui ne l’est pas

L’état public vérifié reste :

\[
43 \le R(5,5) \le 46.
\]

Le projet n’a pas encore prouvé la valeur exacte de `R(5,5)`.

Jalons réellement obtenus :

- témoin à 42 sommets vérifié dans Lean, donc `R(5,5) ≥ 43` ;
- CNF canonique de `K_43` auditée : 903 variables, 1 925 196 clauses ;
- réduction structurelle à 1 509 branches serrées ;
- les 313 types de la strate `d=20,c=10` sont UNSAT côté solveur ;
- deux feuilles disposent d’un LRAT rejoué dans Lean ;
- la feuille difficile `t312 = W5` est certifiée par une preuve LRAT
  reproductible bit pour bit ;
- un certificat Lean vérifie les 206 003 extensions candidates des catalogues
  `R(3,5,n)` jusqu’à `n=10`, dont 8 989 valides ;
- un certificat Lean vérifie les 320 automorphismes et les 1 024 signatures
  de la symétrie W5.
- le théorème Lean `r35_catalogue_order_ten_complete` prouve désormais que le
  catalogue `R(3,5,10)` est sémantiquement exhaustif à isomorphisme fort près ;
- le théorème `r35_catalogues_complete` couvre de la même manière tous les
  niveaux enregistrés de 0 à 10. La preuve inclut suppression du dernier
  sommet, transport du masque, invariance de validité et composition des
  permutations.

Obligations encore ouvertes :

1. relier cette exhaustivité des catalogues au découpage complet des branches
   de la CNF `K43` et au prédicat Ramsey abstrait ;
2. relier formellement les compteurs, comparateurs lexicographiques et
   contraintes de régularité à l’existence d’un graphe ;
3. formaliser la couverture des degrés/codégrés et les bornes extrémales ;
4. produire et rejouer les certificats des autres feuilles ;
5. composer le tout en un théorème final sur le prédicat Ramsey.

Ne jamais présenter les résultats actuels comme `R(5,5)=43`.

## 2. Contenu de l’archive complète

L’arborescence reproduit les chemins relatifs nécessaires à Lean :

```text
R55_REPRISE_2026-08-06/
├── README_REPRISE.md
├── PROMPT_REPRISE_CODEX.md
├── ETAT_PREUVE.md
├── VERIFY_AND_SMOKE_TEST.ps1
├── SHA256SUMS.txt
├── MANIFEST.json
├── bin/windows/cadical.exe
├── r55/
│   ├── sources Python et tests
│   ├── catalogues graph6 et manifestes
│   ├── journaux de campagne JSONL
│   ├── r55_n43_base.cnf
│   ├── min_d20_c10.cnf
│   ├── min_d20_c10_t0.lrat
│   ├── hard_d20_c10_t312_reglex_w5.cnf
│   └── hard_t312_reglex_w5.lrat
└── vendor/lrat-catcher/
    ├── sources du vérificateur
    └── modules Lean R35/R55 ajoutés au projet
```

Les nombreux CNF expérimentaux obsolètes ne sont pas inclus. Ils représentent
environ 2,5 Go et sont tous régénérables.

## 3. Première opération sur le nouveau PC

1. Copier l’archive complète.
2. Calculer son SHA-256 et le comparer au hash annoncé à côté du lien de
   téléchargement.
3. Extraire l’archive dans un chemin court, par exemple `C:\R55`.
4. Ouvrir PowerShell dans le dossier extrait.
5. Exécuter :

```powershell
Set-ExecutionPolicy -Scope Process Bypass
.\VERIFY_AND_SMOKE_TEST.ps1 -HashesOnly
```

Le script compare chaque fichier à `SHA256SUMS.txt`. Une seule divergence
signifie qu’il faut recopier l’archive avant de continuer.

## 4. Environnement exact utilisé

- Windows x86-64 ;
- Python 3.12.13, sans dépendance Python externe ;
- Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622` ;
- Lake 5.0.0 ;
- CaDiCaL 2.1.2 ;
- LRAT-Catcher, base Git
  `4ec2168b810636e789da3349ab3e670af338187c` ;
- les modules Lean R35/R55 locaux sont non publiés et sont inclus dans
  l’archive.

### Python

Installer Python 3.12 ou plus récent, puis vérifier :

```powershell
python --version
cd r55
python -m unittest test_catalog_certificate test_ramsey test_pilot_runner
python catalog_certificate.py verify . r35_extension_certificate.json
```

Résultat attendu : 37 tests réussis et

```text
{"catalogue_graphs": 912, "max_order": 10, "valid_extensions": 8989}
```

### Lean

Installer `elan`, puis laisser le fichier `lean-toolchain` sélectionner
Lean 4.30.0 :

```powershell
& .\bin\windows\elan-init.exe -y `
  --default-toolchain leanprover/lean4:v4.30.0
cd vendor\lrat-catcher
elan toolchain install leanprover/lean4:v4.30.0
lake --version
```

L’installateur Elan est fourni, mais le téléchargement de la toolchain Lean
nécessite Internet. La toolchain complète n’est pas incluse car elle occupe
2,82 Go.

Contrôle rapide des certificats de catalogue et W5 :

```powershell
lake build LRATCatcher.Tests.R35CatalogCertificate `
           LRATCatcher.Tests.R35CatalogCompletenessCore `
           LRATCatcher.Tests.R35CatalogCompleteness `
           LRATCatcher.Tests.R35CatalogCheckpoint `
           LRATCatcher.Tests.R55W5Symmetry
```

Résultat attendu : build réussi. Le mode par défaut utilise `native_decide`,
donc la base de confiance est le noyau Lean plus le compilateur.

Contrôle complet des deux feuilles LRAT importées :

```powershell
lake env lean LRATCatcher/Tests/R55Branch.lean
```

Durée observée : environ 4 minutes. Le théorème important est
`r55_d20_c10_t312_w5_unsat`.

Diagnostic détaillé de la preuve W5 :

```powershell
lake env lean --run LRATCatcher/Tests/R55Diagnose.lean
```

Résultat attendu :

```text
diagnostic result=success
```

## 5. Reproduction de la feuille difficile W5

Depuis `r55`, avec le `cadical.exe` fourni :

```powershell
..\bin\windows\cadical.exe `
  --lrat --no-binary --unsat --walk=false -c 1000000 `
  hard_d20_c10_t312_reglex_w5.cnf `
  reproduction.lrat
```

CaDiCaL doit sortir avec le code 20 et annoncer `UNSATISFIABLE`.

Hashes attendus :

```text
CNF  2263EB489E72CF2AA3688F554FD3301590094B09880200A842ACBEB308AB880F
LRAT B82FE815F61F28AC474F52D79448B760AECF72A377B9E2AD21AA98059A7A1688
```

Le LRAT a été régénéré une seconde fois et son hash était identique bit pour
bit.

## 6. Commandes de travail principales

Régénérer la CNF W5 :

```powershell
cd r55
python ramsey.py write-typed-case-cnf `
  43 5 20 r35_10.g6 312 hard_d20_c10_t312_reglex_w5.cnf `
  --max-colour-degree 24 `
  --degree-encoding rooted `
  --d20-c10-regularity `
  --signature-lex `
  --w5-first-signature-symmetry
```

Régénérer et vérifier le certificat des catalogues :

```powershell
python catalog_certificate.py generate . 10 r35_extension_certificate.json
python catalog_certificate.py verify . r35_extension_certificate.json
python catalog_certificate.py write-lean-data `
  . r35_extension_certificate.json `
  ..\vendor\lrat-catcher\LRATCatcher\Tests\R35CatalogData.lean
```

Attention : tout changement d’une CNF ou d’un LRAT exige une compilation
directe du fichier Lean importeur. Lake ne suit pas ces fichiers externes
comme dépendances.

## 7. Prochaine tâche mathématique recommandée

Ne pas refaire l’exhaustivité des catalogues : elle est maintenant fermée dans
`R35CatalogCompleteness.lean`. Le point d’entrée vérifié est :

```lean
r35_catalogues_complete :
  ∀ order, order ≤ extensionWitnesses.length →
    StrongCatalogueComplete order (catalogues.getD order [])

r35_catalogue_order_ten_complete :
  StrongCatalogueComplete 10 (catalogues.getD 10 [])
```

La prochaine priorité est le pont entre ce théorème sémantique et le découpage
SAT de `K43`. Il faut formaliser :

1. la couverture des degrés et codégrés qui conduit aux 1 509 branches ;
2. la complétude des compteurs de cardinalité, de la régularité et des
   comparateurs lexicographiques ajoutés aux CNF de branche ;
3. la couverture propositionnelle des 313 types `d=20,c=10`, en utilisant
   `r35_catalogue_order_ten_complete` pour justifier les représentants ;
4. la composition des feuilles LRAT avec le prédicat Ramsey abstrait.

Le module `R35CatalogCheckpoint.lean` importe toute la chaîne de complétude en
une seule fois et constitue le contrôle d’intégration rapide à relancer après
toute modification.

## 8. Pièges déjà rencontrés

- Une ancienne CNF W5 contenait dix tautologies. Le parseur Lean les retirait,
  ce qui décalait les identifiants LRAT. La CNF actuelle est normalisée.
- Quatre clauses entières identiques restent présentes volontairement ; elles
  ne sont pas filtrées et ne décalent pas les identifiants.
- Un statut `UNSAT` de CaDiCaL sans LRAT rejoué n’est qu’un résultat de
  recherche, pas une preuve formelle.
- Les cubes fondés sur des représentants canoniques ne couvrent pas
  propositionnellement toutes les valuations avant relabellisation. Leur
  couverture doit passer par un théorème sémantique Lean.
- `lrat_reflect` en mode natif expose un axiome `native_decide` sous
  `#print axioms`. Le mode `+kernel` réduit la base de confiance mais peut être
  beaucoup plus coûteux.

## 9. Sources publiques

- Catalogue Ramsey : https://users.cecs.anu.edu.au/~bdm/data/ramsey.html
- Borne `R(5,5) ≤ 46` : https://arxiv.org/abs/2409.15709
- LRAT-Catcher : https://github.com/leansolving/lrat-catcher
