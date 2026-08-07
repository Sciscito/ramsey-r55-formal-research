# Handoff — recherche R(5,5) / R(4,5,25)

## Mise a jour prioritaire - fin du 7 aout 2026

Cette mise a jour est la source de verite et remplace les anciens compteurs
7/13 cover6 et 1 509 branches actives encore conserves plus bas.

1. Cover6 d8 complet au niveau solveur. Les 13/13 residuelles gelees sont
   parsees, rehachees, controlees pour leurs 21 unites et UNSAT_WITHOUT_PROOF.
   Une reimplementation deterministe autonome reconstruit maintenant les
   3 367 437 clauses source dans leur ordre, puis les 13 simplifications,
   dedoublonnages et ajouts des 21 unites, avec comparaison octet par octet.
   Elle controle aussi exhaustivement les 2^21 affectations locales : 923 012
   sont R(4,4) et les cubes rejettent exactement les 25 200 motifs attendus.
   Rapport SHA-256
   5D8D129A2431B7F473AF24B4BE21864FA6CCBE05DB4D347665FCE0749EB35024.
   Cette voie partage les representants et hashes geles : elle ferme l'audit
   fini CNF, pas un audit a faible mode commun ni le pont mathematique.
   Le module Lean `R44Cover6MotifBridge` decode par ailleurs les six graph6,
   controle les trois paires complementaires et prouve l'equivalence entre le
   bloqueur DIMACS complet de 21 litteraux et l'occurrence induite. Il reste a
   relier les cubes partiels et la formule globale a ce bloqueur.
   Total : 19 657 663 clauses,
   1 077 652 051 octets, 9 889 conflits. Manifeste formule SHA-256
   DDAF42888C6A77C432EC9AA4799D6A24EEDB2088AA25C97C251A82D3986DFB8C;
   batch SHA-256
   AA5E11028D9B8A228E2F6EB7E5F11D0C740BBFDEED9315134C3F1DED8BB1E492.
   Aucun LRAT cover6 et aucun theoreme universel ne sont encore revendiques.
2. Strate minimum-anchor d20,c10 vide. Le record officiel unique
   R(4,5,20,e=100) a les degres 9^2 10^16 11^2, donc aucun voisinage de
   minimum 10. SHA du record :
   D1D1FF46BD5D153B51D7DA094F6BF459BCEAEFDA65EB4941EAD0BB9B09C897CD.
   Totaux corriges : K43 1509 -> 1196; squelette K45 1815 -> 1502.
3. Ecran K43 negatif mais informatif. Sur huit feuilles representatives,
   une est UNSAT sans LRAT (95 conflits) et sept sont UNKNOWN a 100 000
   conflits. Toutes les CNF temporaires ont ete supprimees. Journal SHA-256
   4B8F4F8ED8A7A937AA0127FB7732F375202E68CDF818EAA6F3EF1D511074A5C6.
4. K45. L'identite d'exces n'elimine aucun degre avec les seules bornes e/E,
   malgre une contrainte de voisinage quasi extremal. La generation brute a
   ete abandonnee et le fichier partiel de 114 449 417 octets nettoye.
5. Chaine jouet semantique fermee. Sur K5, l'encodage declaratif de l'absence
   de triangle monochromatique et de P3 positif induit donne exactement 80
   clauses; le LRAT CaDiCaL est rejoue dans Lean jusqu'au theoreme terminal.
   Les tests mutants rejettent notamment, avant replay, une formule rendue
   trivialement UNSAT par une clause vide; un certificat valide eventuel ne
   pourrait donc pas masquer cette mauvaise formule. Le rejeu Lean est force
   hors cache avec `lake env lean`. Ceci valide le noyau declaratif au niveau
   4 pour le jouet seulement, pas les etapes deux-centres de cover6.
6. Quotient K45 catalogue-relatif. Le bloc exclusif d'une arete est R(4,4).
   Ce lemme local est maintenant un theoreme Lean niveau 4 dans
   `R55ExclusiveBlockR44`; le quotient qui l'utilise ne l'est pas.
   Des covers explicites des copies locales gelees des catalogues officiels
   d'ordres 10 et 11, rejoues par une implementation independante, reduisent
   conceptuellement 1 502 types a 112 obligations motif-conditionnees, ou 126
   si la fermeture par complement est imposee. Niveau 1 : aucun pont K45,
   aucune fermeture SAT et aucune completude de catalogue formelle ne sont
   revendiques. Le total 112 depend aussi du cover5 d'ordre 12 et de la vacuite
   d20,c10.

Artefacts lourds :
S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover5-closed-universal\cover6_closed_two_center_d8
et
S:\CodexResearchCache\ramsey-r55-k43-screen\pilot-v1.
Les catalogues et rapports du nouveau pilote restent sous
S:\CodexResearchCache\ramsey-formal\catalogues.
L'archive officielle r45extreme.tar.gz reste sur S: (90 599 728 octets,
SHA-256
9CFAC9DBD1C209CFA342E5D5424DF2A7A3FBB008CA00BF0A992E5BBE72F925B6).

Prochaine sequence recommandee :

1. relire le rapport de replay exact et conserver son test exhaustif local
   comme garde-fou de la provenance F8 -> F(p,q);
2. terminer le pont DIMACS/polarites/unites/deux-centres et composer en Lean
   la disjonction des six motifs deja materialises;
3. produire les 13 LRAT cover6-d8 seulement apres fermeture de ce pont,
   puis les rejouer et composer le theorem d8;
4. traiter cover6 d7 puis d6 et le transport par complement;
5. pour K45, implementer une seule obligation motif-conditionnee sans
   `signature_lex` et mesurer son gain face a la branche typee; arret sans
   extension si le gain est inferieur a x2;
6. pour K43, conserver DLS13 et la coupure additive comme conjectures a
   falsifier, sans augmenter aveuglement les budgets.

Fichiers suivis a lire en premier :
docs/R45_D20_C10_MINIMUM_ANCHOR_VACUITY_2026-08-07.md,
r55/K43_SCREEN_2026-08-07.json et
scripts/r45_d12_cover9_universal/COVER6_D8_CHECKPOINT13.json. Lire aussi
docs/R44_COVER6_D8_SEMANTIC_TARGET_2026-08-07.md et le manifeste leger
scripts/r45_d12_cover9_universal/toy_cover6/MANIFEST.json, puis
docs/R45_EXCLUSIVE_R44_MOTIF_QUOTIENT_2026-08-07.md et
scripts/r45_d12_cover9_universal/R44_SMALL_ORDER_MOTIF_COVERS_2026-08-07.json.

Validation du checkpoint courant :

- suite Python cover9-universal canonique : 93 tests PASS, 2 externes ignores,
  135,32 s;
- jouet : 12 modeles R(3,3)-libres, 0 contre-exemple, identites du manifeste,
  CNF, LRAT, source Lean et programme controlees;
- build cible et compilations Lean directes : PASS pour
  `R44Cover6ToyChain`, `R44Cover6MotifBridge` et `R55ExclusiveBlockR44`;
  aucun `sorry`/`admit`;
- rejeu catalogue final : 103 706 + 546 356 records R(4,4), zero trou,
  70,65 s; rapport SHA-256
  B85E57FA3D7D25A901DD98E387264B8B47FB6CC71F8721FA7CD07BD7DC1E3203;
- manifeste structural SHA-256
  C17EA950F1E02AAF1223AA9E230208498D2ADC7AAA7077A488435D371FE8B614;
- parse PowerShell, AST Python, JSON et whitespace : PASS.

Le `verify-source.ps1` historique complet n'a pas ete relance : il rehache et
rejoue notamment 2,4 Gio de preuves sans rapport avec les fichiers modifies.
Les chemins touches ont ete testes directement, et le script integre desormais
les trois modules Lean avec compilation forcee hors cache.

Checkpoint scientifique du 7 août 2026. Ce fichier est la source de reprise
condensée pour la prochaine conversation. Les rapports spécialisés gardent les
tables complètes.

## Git et stockage

- Dépôt local :
  `C:\Users\migra\Documents\Codex\2026-08-06\on-va-reprendre-de-la-recherche\work\ramsey-r55-formal-research-lf`
- Remote : `git@github.com:Sciscito/ramsey-r55-formal-research.git`
- Branche : `agent/r45-d12-guarded-master`
- PR brouillon a mettre a jour : <https://github.com/Sciscito/ramsey-r55-formal-research/pull/2>
- Commit de depart audite : `84ae9d865258b8a4a1358b63f2f3256965627d5e`
- Règle stricte : Git ne contient que sources, petits certificats, manifests et
  rapports. Toutes les CNF, LRAT, sorties solveur et données temporaires lourdes
  restent sous `S:\CodexResearchCache\ramsey-formal`.
- Dernier audit avant intégration : aucun fichier source supérieur à 10 MiB.
  Les 13 LRAT cover9 totalisant 222 740 623 octets sont tous sur `S:`.
  `.lake\build` et les builds vendor sont des jonctions vers `S:`.
- Espace libre au dernier audit : C: 6,06 GiB ; S: 464,88 GiB.

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

L'ancienne formulation « CNF d8 doublement vérifiée » était trop forte. Le
fichier gelé compte 3 367 438 lignes et 189 298 232 octets, SHA
`64E411A23778972A85DE7C8613A1977F98115E2EC3C9B1711D129932A4ECBB5A`,
et l'ancien vérificateur contrôlait seulement syntaxe, dimensions et hash.
La lacune est désormais fermée par `exact_replay_cover6_d8.py`, une
réimplémentation déterministe autonome qui reconstruit la source ordonnée et
les treize réductions, puis les compare octet par octet. Son rapport suivi
`COVER6_D8_SEMANTIC_REPLAY_V1.json` a pour SHA-256
`5D8D129A2431B7F473AF24B4BE21864FA6CCBE05DB4D347665FCE0749EB35024`.
Cette voie partage les représentants et les hashes gelés : elle réduit le mode
commun du code, mais n'est pas présentée comme une dérivation indépendante.

Les 13/13 résiduelles existent désormais, contiennent chacune les 21 unités
attendues et ont rendu `UNSAT_WITHOUT_PROOF`. Le snapshot 7/13
`COVER6_D8_CHECKPOINT7.json` et ses hashes restent un journal historique,
supersédé par `COVER6_D8_CHECKPOINT13.json`. Aucun LRAT n'a été demandé.

Aucun LRAT cover6, composition Lean des branches ou résultat universel complet
n’est revendiqué.

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

1. conserver vert le replay exact de la source d8 et de ses 13 réductions ;
2. formaliser le pont DIMACS, unités, deux centres et disjonction des motifs ;
3. produire les 13 LRAT et les rejouer seulement après ce pont ;
4. générer/certifier d7 (17 cas), puis d6 (20 cas) ;
5. formaliser le transport global par complément `d ↔ 11-d` ;
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
& $py -B -m scripts.r45_d12_cover9_universal.exact_replay_cover6_d8 preflight
& $py -B -m scripts.r45_d12_cover9_universal.exact_replay_cover6_d8 all --artifact-root $out6
```

Les 13 cas sont déjà produits et leur replay exact est acquis. Avant tout LRAT,
rehacher le rapport suivi, rejouer `exact_replay_cover6_d8 all`, puis relier la
formule exacte aux objets graphes/motifs dans Lean. Le runner refuse d’écraser
un batch : choisir un nouveau `--batch-name`.

## Sources primaires pour l’audit

- intervalle public : <https://arxiv.org/abs/2409.15709>
- catalogue : <https://users.cecs.anu.edu.au/~bdm/data/ramsey.html>
- construction historique : <https://users.cecs.anu.edu.au/~bdm/papers/r45.pdf>
- formalisation HOL4/ITP :
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.16>

## Validation finale historique du checkpoint precedent

Les lignes suivantes décrivent le checkpoint `bf8628d...` et l'ancienne PR 1;
elles sont conservées comme journal historique et ne sont pas l'état
courant défini en tête de fichier.

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
