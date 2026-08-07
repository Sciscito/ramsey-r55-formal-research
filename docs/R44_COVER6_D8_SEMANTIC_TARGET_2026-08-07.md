# Cible sémantique exacte de `cover6-d8` et chaîne jouet

Date : 2026-08-07.

## Énoncé mathématique visé

Soit \(G=(V,E)\) un graphe simple avec \(|V|=12\). Posons

```text
R44(G) :⇔ G ne contient ni K4 ni ensemble indépendant de taille 4.
```

Soit `M6` l'ensemble des six classes d'isomorphisme d'ordre 7 données, en
adjacence graph6 brute, par

```text
F@h^g, FKDhw, FG`Xo, FdW}w, FHFLw, FIIXw.
```

Les paires consécutives sont complémentaires. Le théorème exact attendu de la
tranche degré 8 est

\[
  \forall G,\ R44(G) \Longrightarrow
  \forall r\in V,\ \deg_G(r)=8 \Longrightarrow
  \exists S\subseteq V,\ |S|=7,\ \exists H\in M6,\ G[S]\cong H.
\]

Une variable Lean vraie ou un littéral DIMACS positif signifie une arête de
`G`; c'est aussi l'adjacence brute des six records graph6. Aucun complément
implicite n'est autorisé dans cet énoncé.

Ce résultat ne serait encore que la tranche `d8`. La fermeture universelle
cover6 demande aussi `d7` et `d6`; la complémentation transporte ensuite
`8↔3`, `7↔4` et `6↔5`, puisque `M6` est fermé par complément.

## Normalisation à deux centres

Après une permutation fixant la racine, on peut supposer

```text
r = 0,
N(0) = {1,...,8},
V \ ({0} ∪ N(0)) = {9,10,11}.
```

Le second centre est le sommet 1. Posons

```text
p = |N(1) ∩ {2,...,8}|,
q = |N(1) ∩ {9,10,11}|.
```

Le stabilisateur de la première normalisation trie séparément ces deux blocs,
de sorte que les voisins de 1 y deviennent des préfixes. La liberté `R44`
donne `p≤3`: quatre voisins communs positifs de 0 et 1 seraient deux à deux
négatifs, donc formeraient un 4-stable. Elle donne aussi
`3≤deg(1)=1+p+q≤8`; ainsi `p+q≥2`, tandis que `q≤3` est immédiat. Les treize
cas exhaustifs sont

```text
(0,2), (0,3),
(1,1), (1,2), (1,3),
(2,0), (2,1), (2,2), (2,3),
(3,0), (3,1), (3,2), (3,3).
```

Lean formalise déjà cette permutation, les bornes et la disjonction dans
`exists_twoCenter_case_permutation`.

## Formule destinée à porter le théorème

La formule conditionnée `F8` a 66 variables et 3 367 437 clauses :

- 717 clauses `R44` après fixation de la racine ;
- 3 210 480 bloqueurs de motifs sur les 7-ensembles ne contenant pas la
  racine ;
- 156 240 bloqueurs projetés sur les 7-ensembles contenant la racine.

Les 25 200 cubes locaux sont exacts, sous les contraintes `R44` locales, sur
les 923 012 affectations valides d'ordre 7. Deux implémentations indépendantes
reconstruisent ce fait fini et la fermeture par complément.

Pour chaque `(p,q)`, la résiduelle est obtenue en simplifiant `F8` par les dix
arêtes supplémentaires du second centre, en supprimant les clauses satisfaites
et les littéraux faux, en dédoublonnant, puis en ajoutant les 21 unités exactes
des deux centres. Les treize fichiers totalisent 19 657 663 clauses et
1 077 652 051 octets. CaDiCaL les déclare tous UNSAT, sans LRAT.

Une réimplémentation déterministe autonome, sans import du générateur du
projet, reconstruit maintenant la source ordonnée et ces treize réductions,
puis compare chaque fichier octet par octet. Elle rejoue aussi l'exactitude
locale sur les `2^21` affectations : 923 012 sont `R44` et les cubes rejettent
exactement les 25 200 masques motifs, sans extra ni manque. Son rapport
`COVER6_D8_SEMANTIC_REPLAY_V1.json` a pour SHA-256
`5D8D129A2431B7F473AF24B4BE21864FA6CCBE05DB4D347665FCE0749EB35024`.
Le code partage les représentants et hashes gelés ; il s'agit d'un audit fini
à chemin de code séparé, pas d'une dérivation à faible mode commun.

## Frontière de confiance actuelle

Les ingrédients ne sont pas encore composés :

1. Le maillon fini Python source `F8 → F(p,q)` est maintenant exact, avec les
   métriques de chaque simplification et dédoublonnage conservées. Il demeure
   extérieur à Lean et partage les constantes gelées avec la génération.
2. `R44Cover6MotifBridge.lean` matérialise les six graphes graph6, vérifie leurs
   trois paires complémentaires et prouve que le bloqueur DIMACS complet de 21
   littéraux est faux exactement sur une occurrence induite étiquetée. Les
   cubes partiels conditionnés et leur expansion dans les 3 367 437 clauses ne
   sont pas encore reliés à ce bloqueur déclaratif.
3. Le décalage DIMACS un-vers-zéro, les polarités, les 21 unités et l'égalité de
   la formule globale ne sont pas encore composés avec `TwoCenterBranch`.
4. Aucun LRAT cover6 n'existe ; aucun des treize UNSAT n'est donc au-dessus du
   niveau 2.
5. La racine arbitraire, le transport par complément, `d6`, `d7` et le gluing
   global `R(4,5,25)` restent séparés.

En conséquence, le théorème `cover6-d8` lui-même demeure une cible, pas un
résultat démontré. Les niveaux 2, 3 et 4 atteints par des sous-maillons ne
s'additionnent pas en un niveau global.

Reproduction ciblée des deux nouveaux maillons :

```powershell
python -B -m scripts.r45_d12_cover9_universal.exact_replay_cover6_d8 preflight
python -B -m scripts.r45_d12_cover9_universal.exact_replay_cover6_d8 all --artifact-root $out6
cd vendor/lrat-catcher
lake env lean LRATCatcher/Tests/R44Cover6MotifBridge.lean
```

## Chaîne jouet fermée

Le jouet vérifie le noyau déclaratif CNF/LRAT/Lean sur l'énoncé non vacu
suivant :

> Toute coloration de `K5` sans triangle monochromatique contient un `P3`
> positif induit.

Il existe exactement 12 colorations `R(3,3)`-libres sur les 1 024
affectations, donc le théorème n'est pas fermé par vacuité. La CNF comporte
10 variables, 20 clauses Ramsey et 60 bloqueurs, un par
plongement injectif étiqueté du `P3`. Une vérification exhaustive indépendante
sur les 1 024 affectations établit séparément l'exactitude du bloc Ramsey et du
bloc motif.

- CNF : 826 octets, SHA-256
  `3B01FC465184466A2B5E9F10966A4E28D3D2CB25D4728B9A1471A5060CC96313` ;
- CaDiCaL 2.1.2 : UNSAT en 14 conflits avec `--checkproof=2` ;
- LRAT : 379 octets, SHA-256
  `EDF122CE124CD6FAF367D5989B024D8E41CB18CD7D0EDDAB287DA179B600C4C5` ;
- égalité Lean exacte entre le DIMACS parsé et la décomposition déclarative :
  `certifiedToyFormula_eq_decomposition` ;
- théorème terminal :
  `every_r33_order_five_contains_induced_positive_p3` ;
- build Lean ciblé : PASS, sans `sorry` ni `admit`.

Les tests négatifs rejettent une polarité Ramsey corrompue, une polarité motif
corrompue, un index DIMACS zéro, un LRAT modifié, et surtout une formule rendue
trivialement UNSAT par une clause vide avant tout replay. Ainsi, même si un
certificat valide était fourni pour cette mauvaise formule, elle ne franchirait
pas le pont déclaratif exact. Le manifeste léger contrôle en outre les tailles
et hashes du CNF, du LRAT, du module Lean et du programme de vérification.

Reproduction légère :

```powershell
python -B -m unittest scripts.r45_d12_cover9_universal.test_cover6_toy_chain
python -B -m scripts.r45_d12_cover9_universal.cover6_toy_chain verify
cd vendor/lrat-catcher
lake build LRATCatcher.Tests.R44Cover6ToyChain
lake env lean LRATCatcher/Tests/R44Cover6ToyChain.lean
```

Cette chaîne jouet atteint le niveau 4 pour son seul énoncé. Elle valide la
forme du noyau déclaratif proposé, pas le générateur cover6-d8 à grande
échelle. Elle n'exerce notamment ni la normalisation à deux centres, ni la
réduction `F8 → F(p,q)`, ni les 21 unités de branche, ni le dédoublonnage, ni
les cubes/orbites des six motifs, ni le transport par complément.
