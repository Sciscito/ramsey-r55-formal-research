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

Le certificat Python compact
`COVER6_CUBE_MOTIF_BRIDGE_V1.json` vérifie un autre maillon fini : les six
représentants ont chacun une unique complétion `R44`, puis l'action de `S7`
donne bijectivement 25 200 cubes et 25 200 masques motifs distincts. Pour le
conditionnement de `F8`, il réduit les blocs sans racine à 334 représentants
d'orbites de stabilisateur et les blocs contenant la racine à 38 représentants
d'orbites projetés, avec les lifts contrôlés dans son modèle Python. Ce
programme importe
`exact_replay_cover6_d8`; ce n'est donc pas une implémentation indépendante.
Sa portée exclut explicitement SAT, LRAT, égalité au DIMACS parsé, rejeu Lean
et théorème `cover6-d8`.

## Frontière de confiance actuelle

Les ingrédients sont désormais composés pour le théorème local `cover6-d8`;
la liste suivante sépare les contrôles finis, le rejeu LRAT et les maillons
sémantiques afin de rendre explicite la base de confiance :

1. Le maillon fini Python source `F8 → F(p,q)` est maintenant exact, avec les
   métriques de chaque simplification et dédoublonnage conservées. Il demeure
   extérieur à Lean et partage les constantes gelées avec la génération.
2. `R44Cover6MotifBridge.lean` matérialise les six graphes graph6, vérifie leurs
   trois paires complémentaires et prouve que le bloqueur DIMACS complet de 21
   littéraux est faux exactement sur une occurrence induite étiquetée.
3. `R44Cover6CubeBridge.lean` compile et prouve génériquement qu'un bloqueur de
   cube partiel est faux exactement lorsque ses bits fixes correspondent. Il
   transforme aussi une hypothèse séparée de sûreté du cube en occurrence de
   motif.
4. `R44Cover6RepresentativeCubes.lean` compile et certifie les six constantes :
   bonne formation, énumération de 16 à 64 complétions, unique complétion
   `R44` et identification de chaque cible par une permutation explicite.
   `R44Cover6S7Transport.lean` prouve désormais l'invariance `R44`, le
   transport bit-à-bit des masques et de `CubeMatchesLocal`, puis le fait que
   tout cube accompagné d'un témoin d'orbite vers l'un des six représentants
   force le motif transporté. Le certificat
   `COVER6_CONDITIONED_ORBIT_WITNESSES_V1.json` fournit maintenant les
   32 880 témoins K7 et 1 200 lifts K6, puis vérifie la vue ordonnée des
   3 514 + 2 409 bloqueurs retenus par le cœur.
   `R44Cover6ConditionedWitnesses.lean` décode ce flux, contrôle les clauses
   et lifts par deux certificats finis agrégés et construit le fournisseur
   sémantique dans Lean.
5. Le décalage DIMACS un-vers-zéro et l'égalité des 6 152 clauses du cœur à la
   sélection de la source Lean sont maintenant formalisés.
   `R44Cover6SemanticComposition.lean` ferme les 717 clauses de base et les
   huit extras, certifie la découpe 221/3514/2409/8, puis compose un
   `CoreBlockerWitnessProvider` avec `TwoCenterBranch` et l'UNSAT du cœur.
   Le module conditionné instancie cet endpoint et prouve le corollaire positif
   `degreeEight_has_cover6_motif`.
6. Un pilote `Master8` exact réunit les treize affectations dans une formule de
   3 367 459 clauses. CaDiCaL la ferme en 4 598 conflits et produit un LRAT
   unique de 128 131 809 octets avec `--checkproof=2`. Le rejeu Lean brut a
   d'abord été arrêté au plafond de 3 Gio avant tout théorème. Une fermeture
   des dépendances, sûre ici parce que les 1 182 841 additions sont toutes
   RUP, réduit ensuite la source à 6 152 clauses et la preuve à 7 061
   additions. Le LRAT remappé et un second LRAT régénéré par CaDiCaL sur le
   cœur sont tous deux acceptés par LRATCatcher. Le mapping vers le DIMACS
   Master8 gelé est une sous-séquence ordonnée exacte.
7. `R44Cover6Master8CoreBridge.lean` prouve génériquement que l'UNSAT d'une
   sélection indexée transfère à la CNF complète.
   `R44Cover6Master8IndexedSource.lean` définit ensuite la source Master8 par
   sections et unranking, vérifie exactement la sélection des 6 152 clauses,
   rejoue le LRAT et prouve `master8Source_unsat`. La taxonomie révèle une voie
   plus simple : `F8` plus sept tris et `-15`, sans unités racine, bornes
   croisées ni treize cas. Cette source a 3 367 445 clauses, SHA-256
   `0133D40DC0458E7CD426F22DA08B525B4197467E539E4446AE94A38E84D7341E`,
   et Lean prouve `normalizedSource_unsat`.
8. La racine arbitraire, le transport par complément, `d6`, `d7` et le gluing
   global `R(4,5,25)` restent séparés.

En conséquence, le théorème local `cover6-d8` est maintenant démontré au
niveau 4 : `isRamseyFree 12 4 4` et un degré positif 8 de la racine 0
impliquent une occurrence induite de l'un des six motifs. Cette conclusion ne
s'étend pas encore à une racine arbitraire dans l'API terminale, aux degrés 6
et 7, au transport global par complément, au gluing `R(4,5,25)` ou à une
nouvelle borne sur `R(5,5)`.

Reproduction ciblée des maillons locaux :

```powershell
python -B -m scripts.r45_d12_cover9_universal.exact_replay_cover6_d8 preflight
python -B -m scripts.r45_d12_cover9_universal.exact_replay_cover6_d8 all --artifact-root $out6
python -B -m scripts.r45_d12_cover9_universal.certify_cover6_cube_motif_bridge check
python -B -m unittest scripts.r45_d12_cover9_universal.test_cover6_conditioned_orbit_witnesses
python -B -m scripts.r45_d12_cover9_universal.master8_prefix_pilot preflight
python -B -m unittest scripts.r45_d12_cover9_universal.test_reduce_master8_lrat_core
python -B -m unittest scripts.r45_d12_cover9_universal.test_master8_core_taxonomy
cd vendor/lrat-catcher
lake env lean LRATCatcher/Tests/R44Cover6MotifBridge.lean
lake env lean LRATCatcher/Tests/R44Cover6CubeBridge.lean
lake env lean LRATCatcher/Tests/R44Cover6RepresentativeCubes.lean
lake env lean LRATCatcher/Tests/R44Cover6Master8CoreBridge.lean
lake env lean LRATCatcher/Tests/R44Cover6Master8IndexedSource.lean
lake env lean LRATCatcher/Tests/R44Cover6S7Transport.lean
lake env lean LRATCatcher/Tests/R44Cover6SemanticComposition.lean
lake env lean LRATCatcher/Tests/R44Cover6ConditionedWitnesses.lean
lake env lean ../../scripts/r45_d12_cover9_universal/master8_core/Replay.lean
```

Le test exhaustif cubes/motifs est activé séparément par
`RAMSEY_COVER6_BRIDGE_FULL=1`; il régénère et compare alors exactement le JSON
compact suivi. Les tests longs du cœur Master8 sont eux aussi opt-in et sont
documentés dans leur module de test. Le recalcul des 34 080 témoins
conditionnés est activé par
`RAMSEY_COVER6_CONDITIONED_WITNESSES_FULL=1`.

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
