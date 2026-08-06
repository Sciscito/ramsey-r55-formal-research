# Prompt à coller dans Codex sur le nouveau PC

Copier tout le bloc ci-dessous dans une nouvelle tâche Codex après extraction
de l’archive complète.

---

Tu reprends un projet de recherche formelle sur le nombre de Ramsey `R(5,5)`.
Commence par lire intégralement `README_REPRISE.md`, `ETAT_PREUVE.md`,
`SHA256SUMS.txt` et les fichiers Lean cités ci-dessous. Ne recommence pas le
projet depuis zéro et ne prétends jamais que `R(5,5)=43` avant composition
formelle complète.

État public au 6 août 2026 : `43 ≤ R(5,5) ≤ 46`.

Objectif final : décider l’existence d’un graphe sur 43 sommets sans `K5` ni
ensemble indépendant de taille 5, avec preuve automatiquement vérifiable.

État local acquis :

1. CNF canonique `K43` : 903 variables, 1 925 196 clauses, SHA-256
   `B2E3A560E6F77EBDA6D1D41C01469738E672701CDAD0E1E98C0557CB88D38C42`.
2. Témoin à 42 sommets vérifié dans Lean : borne inférieure `R(5,5)≥43`.
3. Manifeste structurel serré : 1 509 branches, SHA-256
   `6480F59552D21446BE448DC50CC85395BB711746193848E3291164CADEFE9E26`.
4. Strate `d=20,c=10` : 313/313 types éliminés côté solveur.
5. Feuille difficile `t312 = W5` :
   - CNF 63 080 variables, 2 049 737 clauses ;
   - CNF SHA-256
     `2263EB489E72CF2AA3688F554FD3301590094B09880200A842ACBEB308AB880F` ;
   - LRAT SHA-256
     `B82FE815F61F28AC474F52D79448B760AECF72A377B9E2AD21AA98059A7A1688` ;
   - diagnostic Lean complet : succès ;
   - théorème `r55_d20_c10_t312_w5_unsat` compilé.
6. Certificat des catalogues `R(3,5,n)`, `n≤10` :
   - 912 graphes ;
   - 206 003 extensions candidates ;
   - 8 989 extensions valides avec permutation explicite ;
   - théorème calculatoire Lean
     `r35_catalogue_extensions_checked` compilé.
7. Symétrie W5 : 320 automorphismes, 1 024 signatures, 39 orbites ; théorème
   Lean `w5_signature_symmetry_checked` compilé.
8. L’exhaustivité sémantique des catalogues est maintenant formalisée :
   - `r35_catalogues_complete` couvre tous les niveaux enregistrés ;
   - `r35_catalogue_order_ten_complete` couvre explicitement l’ordre 10 ;
   - la relation utilisée est `GraphIsomorphicFin`, avec vraie permutation
     finie et composition prouvée.
9. Le module d’intégration `R35CatalogCheckpoint.lean` compile.
10. 37 tests Python passent.

Fichiers prioritaires :

- `r55/ramsey.py`
- `r55/catalog_certificate.py`
- `r55/r35_extension_certificate.json`
- `vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogCertificate.lean`
- `vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogCompletenessCore.lean`
- `vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogCompleteness.lean`
- `vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogStrongInduction.lean`
- `vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogMaskTransport.lean`
- `vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogValidityInvariant.lean`
- `vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogCheckpoint.lean`
- `vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogData.lean`
- `vendor/lrat-catcher/LRATCatcher/Tests/R55W5Symmetry.lean`
- `vendor/lrat-catcher/LRATCatcher/Tests/R55Branch.lean`

Avant toute modification :

1. exécute `VERIFY_AND_SMOKE_TEST.ps1 -HashesOnly` ;
2. lance les 37 tests Python ;
3. construis `LRATCatcher.Tests.R35CatalogCheckpoint` et le module W5 ;
4. lis les commentaires et obligations non prouvées.

Tâche immédiate : ne refais pas la complétude des catalogues. Lis et construis
`R35CatalogCompleteness.lean`, dont le théorème final est :

```lean
r35_catalogue_order_ten_complete :
  StrongCatalogueComplete 10 (catalogues.getD 10 [])
```

Poursuis le pont entre cette exhaustivité et la couverture du découpage SAT de
`K43` : degrés/codégrés, compteurs de cardinalité, régularité, lexicographie,
1 509 branches serrées et 313 types `d=20,c=10`. La priorité est d’obtenir un
théorème Lean disant que toute coloration `K43` évitant les deux `K5` tombe
dans au moins une branche certifiée, puis de composer les LRAT de ces feuilles.

Contraintes de rigueur :

- séparer clairement résultats de recherche SAT et théorèmes vérifiés ;
- ne pas faire confiance à nauty ou à Python dans la base finale : les
  permutations doivent être contrôlées dans Lean ;
- préserver les hashes des CNF/LRAT déjà certifiés ;
- après toute modification d’un certificat externe, recompiler directement
  son importeur Lean ;
- conserver une liste explicite des obligations restantes ;
- poursuivre de manière autonome, avec tests et preuves proportionnés.

L’architecture SAT recommandée est une base canonique partagée avec bits de
branche et 313
cubes préfixes couvrants, puis des LRAT autonomes par feuille composés par
LRAT-Catcher.

---
