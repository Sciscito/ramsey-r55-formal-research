# Handoff — recherche R(5,5) / R(4,5,25)

Checkpoint scientifique du 7 août 2026. Ce fichier est la source de reprise
condensée pour la prochaine conversation. Les rapports spécialisés gardent les
tables complètes.

## Git et stockage

- Dépôt local :
  `C:\Users\migra\Documents\Codex\2026-08-06\on-va-reprendre-de-la-recherche\work\ramsey-r55-formal-research-lf`
- Remote : `git@github.com:Sciscito/ramsey-r55-formal-research.git`
- Branche : `agent/r45-d12-guarded-master`
- PR brouillon : <https://github.com/Sciscito/ramsey-r55-formal-research/pull/1>
- Commit de ce checkpoint : `bf8628d83b2816ca7cdc82a43ed02b39a881b6be`
- Règle stricte : Git ne contient que sources, petits certificats, manifests et
  rapports. Toutes les CNF, LRAT, sorties solveur et données temporaires lourdes
  restent sous `S:\CodexResearchCache\ramsey-formal`.
- Dernier audit avant intégration : aucun fichier source supérieur à 10 MiB.
  Les 13 LRAT cover9 totalisant 222 740 623 octets sont tous sur `S:`.
  `.lake\build` et les builds vendor sont des jonctions vers `S:`.
- Espace libre au dernier audit : C: 2,84 GiB ; S: 465,42 GiB.

## État scientifique global et non-revendications

L’intervalle public vérifié reste `43 ≤ R(5,5) ≤ 46`. Aucune nouvelle borne
de Ramsey n’est obtenue ici. Le projet formalise et décompose `R(4,5,25)`,
ingrédient de l’attaque de `R(5,5)`.

Deux notions de « degré 8 » doivent rester distinctes :

1. la branche globale degré rouge 8 de `R(4,5,25)` est déjà fermée de bout en
   bout par la chaîne Lean/LRAT antérieure ;
2. la tranche degré-racine 8 d’un graphe auxiliaire `R(4,4,12)` est la tranche
   nouvellement certifiée pour la cible universelle cover9.

Pour la branche globale degré 12 de `R(4,5,25)`, le compteur demeure
**0/12 cas mathématiques fermés**. Le scaffold Lean `1+12+12`, les 12 types
`R(3,5,12)`, la permutation globale, les 66 unités gauche et les polarités
droite sont formels, mais aucune des 12 feuilles globales n’est entièrement
réfutée.

## Résultats vérifiés à conserver

### 1. Minimum général cover5 d’ordre 7

Cinq motifs d’ordre 7 couvrent les 1 449 166 enregistrements de la source
gelée `r44_12.g6`. Un noyau explicite de 25 graphes et une CNF no-cover4 avec
LRAT rejoué par Lean excluent toute couverture de taille au plus 4.

- SHA cover :
  `CEAE61F737722C6D1392B5C8D654FC1B09D482AA3C76222EE2D9CBFF3CA5E288`
- témoin induit :
  `36EC5E95D8599F6AE8099A6D3376D0E3F43269059FC644A1A3F96C52846414CB`
- LRAT no-cover4 :
  `4FD1F02297F5019B9EADBE9BC20E29DF326B0B7F99B8A539C140FD9911F15793`
- théorème :
  `R45OrderSevenCoverMinimumReplay.no_order7_cover_of_size_four`

Portée : minimum exact parmi les motifs d’ordre 7 sur le catalogue gelé ;
aucun minimum mixte ordre 7/8 n’est revendiqué.

### 2. Cover9 universel, tranche R(4,4,12) de degré 8

La formule universelle ne lit pas `r44_12.g6`. Elle encode les 990 clauses
`R(4,4)` de `K_12` et interdit neuf motifs induits sur les 792
sous-ensembles d’ordre 7.

- maître réduit : 11 976 030 clauses,
  SHA `425676A0876F06BCE2D3477BB6D11A566D77C6DD7D7FD46E9A1B07D8E5C1C098`
- bloc degré 8 : 1 750 101 clauses,
  SHA `3CE0350607818AEE8CFD3F365316286D2EEC8985FB6A2056953A58FB34DC27DB`
- split à deux centres : 13 cas exhaustifs
- résultat : 13/13 UNSAT, 13/13 LRAT CaDiCaL rejoués par LRAT-Catcher/Lean
- LRAT : 222 740 623 octets au total ; maximum 42 141 609 octets
- manifeste portable :
  `scripts/r45_d12_cover9_universal/TWO_CENTER_CERTIFICATES.json`
- SHA manifeste :
  `77FE47B5BC73865EDB0405DFC2D3B0A367C2A757B27A83CDC981D5958F80DE23`

Le cas `p2q0` a été reconstruit sans import du générateur : `2^21` graphes,
923 012 `R(4,4)`, 1 750 101 clauses source puis 758 924 résiduelles,
44 764 698 octets, SHA CNF
`D9CF9356230E6624BED5AB3AC58FACDC98AE96428CF953BD5F8DB1EB3284D315`.
Son LRAT, régénéré trois fois bit-identique, a pour SHA
`4C65A4480E9BDD8B0F526DE496A774795905C23DD1067D1B4574D267388403C5`.

Les modules Lean
`R44OrderTwelveRootSymmetry`,
`R44OrderTwelveRootSymmetryTransport`,
`R44OrderTwelveDegreeBounds`,
`R44OrderTwelveTwoCenterSymmetry` et
`R44OrderTwelveTwoCenterCases` formalisent une vraie permutation fixant la
racine, les bornes de degré, la normalisation du second centre, les 13 cas
exacts et le transport `R(4,4)`/motifs. Théorème central :
`exists_twoCenter_case_permutation`.

Frontière exacte : CNF résiduelles et split graphe sont certifiés séparément.
Il manque le pont Lean pour la réduction locale, la restriction/dédoublonnage
DIMACS et chaque `TwoCenterBranch`, puis la composition des 13 replays. Les
degrés cover9 3 à 7 ne sont pas certifiés.

### 3. Minimum exact sous fermeture par complément : cover6

Résultat principal nouveau : le minimum sous fermeture par complément est
exactement trois paires, donc six classes de motifs d’ordre 7, pour le
catalogue officiel `R(4,4,12)` gelé.

| IDs officiels, base 0 | paire graph6 | tailles d’orbite |
|---:|---|---:|
| 41, 220 | `F@h^g`, `FKDhw` | 5 040 + 5 040 |
| 174, 323 | <code>FG&#96;Xo</code>, `FdW}w` | 2 520 + 2 520 |
| 185, 194 | `FHFLw`, `FIIXw` | 5 040 + 5 040 |

- upper direct : 1 449 166 / 1 449 166, zéro trou
- TSV SHA :
  `404E49E3218424FCB73314ADEE42CC873CD3F8D67E4615653A8BC0210F61AD16`
- fermeture : 25 200 masques, SHA
  `04B9688924BFC2EF6F92FB5734B19E7E771C37446DD3E442ECED8648BE1CBDD7`
- noyau : 30 graphes, SHA
  `EB61306B5DA0F15DC1112D82007BB29CD2FD3AEE460FD1C0D62E24401C66C8CC`
- signatures :
  `FD92B41FAD600EEC47FA5214EA1F36D9E7B1B6D44DDBE8EADFD029F41EFD89A9`
- manifeste suivi : SHA
  `B27CD8D1F0FF5D6E58B67AC9F0B74FE5139D932698D9F1AFD8DF0C64A2AE8FCF`
- trous après retrait des paires : `(22, 446, 40)`

Le replay inférieur énumère les `2^21` graphes d’ordre 7, retrouve 923 012
`R(4,4)` et 362 classes, reconstruit 181 paires sans point fixe, vérifie les
30 graphes du noyau comme `R(4,4,12)`, recalcule 23 760 sous-graphes induits
et exclut les 16 471 choix d’au plus deux paires. Le noyau est
deletion-irréductible.

Le replay upper standard-library scanne les 1 449 166 graphes et leurs 792
sous-ensembles sans incidence ni témoin : PASS en 167,14 s. Premier-hit :
`(46 679, 347 807, 698 002, 36 774, 108 486, 211 418)`.

La borne inférieure est absolue sur 30 graphes valides explicites. L’upper est
relatif au catalogue gelé tant que son exhaustivité n’est pas reliée à une
preuve universelle. L’audit ciblé n’a pas retrouvé ce résultat, mais aucune
priorité mondiale n’est revendiquée sans audit bibliographique élargi.

### 4. Route universelle cover6 fermée par complément

Le complément réduit les degrés racine `3..8` aux représentants `6,7,8`.
Deux implémentations indépendantes, sans catalogue K12, valident
exhaustivement 923 012 affectations locales `R(4,4)`, 25 200 motifs et
25 200 cubes partiels exactement équivalents sur ce domaine.

- SHA cubes :
  `0239E74AC009B28173E59C3293F7F9C9370A99832B19BB28205EF449E6238F7D`
- largeurs : 15 → 5 040, 16 → 10 080, 17 → 10 080
- d6 : 4 858 890 clauses, 20 cas à deux centres
- d7 : 4 312 419 clauses, 17 cas
- d8 : 3 367 437 clauses, 13 cas

La CNF d8 est doublement vérifiée : 3 367 438 lignes, 189 298 232 octets,
SHA
`64E411A23778972A85DE7C8613A1977F98115E2EC3C9B1711D129932A4ECBB5A`.

Pour geler rapidement la conversation, 7/13 résiduelles ont été générées et
vérifiées, chacune avec 21 unités exactes :
`(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)`. Les six cas
`(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)` restent à produire.

Les 7 pilotes CaDiCaL 2.1.2 ont rendu `UNSAT_WITHOUT_PROOF`, entre 58 et
609 conflits et 2,34–3,30 s par cas. Aucun LRAT n’a été demandé. Le snapshot
suivi `COVER6_D8_CHECKPOINT7.json` a pour SHA
`7DEB286B0E9729B0C8C16A2F69EC4503870D32D37D7A3B7C6ABDCCE03101EF29`.
Il fige le manifeste partiel externe
`8036E96769D6F6EEFDB5D1C653EFD57141235B863BC7290B8A61BB1EE7A0A534`
et le batch
`ABCC63345BD1278C630F0BFDBECA086EA629BA00C3A2A1D043C7E5DE643BDCE3`.

Aucun LRAT cover6, pont Lean ou résultat universel complet n’est revendiqué.

## Pistes négatives — ne pas répéter sans idée nouvelle

Gluing global degré 12 de `R(4,5,25)` :

- feuille type 0 : `UNKNOWN` à 1 M puis 5 M conflits ;
- variantes degré/lexicographiques : `UNKNOWN`, plus lentes ;
- split enraciné `R(3,4)` : `UNKNOWN`, plus lent ;
- split d’une ligne en 81 cubes : 81/81 `UNKNOWN` à 50 k ;
- motif dominant à deux centres × 81 : 81/81 `UNKNOWN` à 200 k,
  16 200 094 conflits cumulés ;
- cinq motifs cover5 sur type gauche 0 : 5/5 `UNKNOWN` à 100 k et 200 k.

Cover9 universel :

- maître et variante préfixe-racine : timeout 300 s, aucun LRAT ;
- cible degré 3 : timeout 300 s ;
- le succès d8 vient du conditionnement de bloc puis du split à deux centres.

Le prototype fermeture brute cover5, 8 classes/30 240 masques, et les scripts
`generate_complement_closed_branches.py` /
`generate_complement_closed_cover5.py` sont historiques et **supersédés**.

## Prochaine priorité, sans dispersion

1. produire les six résiduelles cover6 d8 manquantes et refaire la vérification
   13/13 ;
2. si les 13 sont UNSAT, produire LRAT + replay Lean ;
3. générer/certifier d7 (17 cas), puis d6 (20 cas) ;
4. formaliser le transport global par complément `d ↔ 11-d` ;
5. formaliser cubes, 792 instanciations, restriction et dédoublonnage CNF ;
6. composer replays et branches Lean ;
7. réinjecter seulement ensuite ce lemme dans les 12 gluings globaux ;
8. audit bibliographique élargi et paquet portable avant publication.

Le seuil d’un article de certificat computationnel devient crédible si la
route cover6 universelle est fermée et la nouveauté confirmée. Le seuil d’une
percée Ramsey majeure n’est pas atteint : aucune nouvelle borne et 0/12
gluings globaux.

## Artefacts SSD — source de vérité

- catalogues :
  `S:\CodexResearchCache\ramsey-formal\sources\mckay-r44`
- cover9 :
  `S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover9-universal`
- cover6 universel, nom historique :
  `S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover5-closed-universal`
- minimum cover6 :
  `S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-complement-closed-minimum`
- temporaire :
  `S:\CodexResearchCache\ramsey-formal\tmp\r45-d12-finalize`
- `r44_7.g6` SHA :
  `6A3DA7F0687C392420F190DB0643B5C5B7ECB1A3C5ED098C7D96200185A5F010`
- `r44_12.g6` SHA :
  `C6A60EE177E00C1168259A5BD464F9CFA5A5B471AE2BA1811E7B3FAF23144E7A`

## Commandes exactes de reprise

```powershell
$repo = 'C:\Users\migra\Documents\Codex\2026-08-06\on-va-reprendre-de-la-recherche\work\ramsey-r55-formal-research-lf'
$py = 'C:\Users\migra\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$lake = 'S:\CodexResearchCache\ramsey-formal\lean-toolchains\leanprover--lean4---v4.30.0\bin\lake.exe'
$src = 'S:\CodexResearchCache\ramsey-formal\sources\mckay-r44'
$out6 = 'S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover5-closed-universal'
$out9 = 'S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover9-universal'
$env:PYTHONDONTWRITEBYTECODE = '1'
$env:TEMP = 'S:\CodexResearchCache\ramsey-formal\tmp\r45-d12-finalize'
$env:TMP = $env:TEMP
Set-Location $repo
git -c "safe.directory=C:/Users/migra/Documents/Codex/2026-08-06/on-va-reprendre-de-la-recherche/work/ramsey-r55-formal-research-lf" status --short
git -c "safe.directory=C:/Users/migra/Documents/Codex/2026-08-06/on-va-reprendre-de-la-recherche/work/ramsey-r55-formal-research-lf" log -1 --oneline
& $py -B -m scripts.r45_d12_complement_closed_minimum.verify_minimum --source7 "$src\r44_7.g6"
& $py -B -m scripts.r45_d12_complement_closed_minimum.verify_cover6 --source12 "$src\r44_12.g6"
& $py -B -m scripts.r45_d12_cover9_universal.consolidate_two_center_certificates --output $out9 --verify-manifest scripts\r45_d12_cover9_universal\TWO_CENTER_CERTIFICATES.json
& $py -B -m scripts.r45_d12_cover9_universal.generate_complement_closed_cover6_branches preflight
& $py -B -m scripts.r45_d12_cover9_universal.verify_complement_closed_cover6_branches preflight
& $py -B -m scripts.r45_d12_cover9_universal.generate_complement_closed_cover6_branches verify --output $out6 --degree 8
& $py -B -m scripts.r45_d12_cover9_universal.verify_complement_closed_cover6_branches formula --output $out6 --degree 8
```

Après production complète des six cas manquants, lancer
`generate_complement_closed_cover6_two_center verify`. Le runner refuse
d’écraser un batch : choisir un nouveau `--batch-name`.

## Sources primaires pour l’audit

- intervalle public : <https://arxiv.org/abs/2409.15709>
- catalogue : <https://users.cecs.anu.edu.au/~bdm/data/ramsey.html>
- construction historique : <https://users.cecs.anu.edu.au/~bdm/papers/r45.pdf>
- formalisation HOL4/ITP :
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.16>

## Validation finale de ce checkpoint

- suite universelle : 72 tests PASS, 1 test externe ignoré, 128,815 s ;
- suite cover6-minimum : 9 tests PASS, 2 tests externes ignorés ;
- replay inférieur externe cover6-minimum : PASS en 17,8 s ;
- scan supérieur direct cover6-minimum : PASS en 167,14 s ;
- consolidation cover9 externe : 13/13, 222 740 623 octets LRAT, PASS ;
- build Lean ciblé : 46 jobs, PASS ;
- scripts/verify-source.ps1 intégral : PASS en 493,1 s, y compris
  rehash/replay du bundle historique de 60 LRAT (2 405 113 598 octets), build
  Lean d’intégration et théorèmes terminaux ;
- audit Lean : aucun sorry, admit, unsafe ou nouvel axiom dans les cinq modules
  de symétrie/deux-centres ; axiomes observés limités aux standards attendus
  et à native_decide ;
- PowerShell parse : PASS ; git diff --check : PASS avant staging ;
- dépôt : zéro __pycache__, zéro fichier source supérieur à 10 MiB ;
- commit scientifique : bf8628d83b2816ca7cdc82a43ed02b39a881b6be ;
- PR : https://github.com/Sciscito/ramsey-r55-formal-research/pull/1