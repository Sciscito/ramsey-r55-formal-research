# Reprise R(5,5) après le crash — 6 août 2026

## Point de départ sûr

Dépôt privé :

`https://github.com/Sciscito/ramsey-r55-formal-research`

Dernier commit de recherche avant ce document :

`95cb35e40039489ce499ac504e6f1b6ce4cfd06e`

Les commits importants de la session sont :

- `018b02f76f62f3841612ab0bf11333bd28e96041` — certification Lean de
  `R(3,5) ≤ 14` ;
- `a972a9537213ad934a7da13d2c9735ce737b6d9a` — réduction d'une
  contre-exemple hypothétique à `R(4,5) ≤ 25` aux degrés 8, 10 ou 12 ;
- `2be8c60101216c4fc6ed455111ec3f3e80702a03` — reconstruction Lean
  exacte du bloc de 116 928 clauses de compteurs de degrés ;
- `95cb35e40039489ce499ac504e6f1b6ce4cfd06e` — paquet reproductible du
  pilote degré 8, avec 54 feuilles sur 54 signalées UNSAT.

## Reprendre sur un autre PC

Cloner le dépôt privé et rester sur `main` :

```powershell
git clone https://github.com/Sciscito/ramsey-r55-formal-research.git
cd ramsey-r55-formal-research
git checkout main
git log -5 --oneline
```

Les gros CNF et LRAT ne sont volontairement pas stockés dans Git. Ils sont
dans la release privée :

`https://github.com/Sciscito/ramsey-r55-formal-research/releases/tag/checkpoint-2026-08-06`

Archive : `R55_REPRISE_COMPLET_2026-08-06.zip`

SHA-256 attendu :

`2A9C34DBB615CB70FB542B7955FED5C19495EC6DE828C1306778B1DF05ADD571`

Pour compiler `R55RootedDegreeBlock.lean`, remettre notamment
`min_d20_c10.cnf` dans le dossier `r55` du clone. Le paquet du pilote
degré 8 est léger et déjà entièrement dans Git sous
`scripts/r45_d8_pilot`.

## État honnête des résultats

| Résultat | Statut | Signification |
|---|---|---|
| `R(3,5) ≤ 14` | preuve Lean | Dépendance classique, vérifiée localement |
| `R(4,4) ≤ 18` | preuve Lean | Déduite par récurrence depuis le LRAT de `R(3,4) ≤ 9` |
| degrés 8, 10 ou 12 pour `K25` | preuve Lean | Réduit le certificat `R(4,5) ≤ 25` à trois cas |
| bloc des 116 928 clauses | preuve Lean | Les compteurs externes sont reconstruits exactement |
| 54/54 feuilles degré 8 UNSAT | résultat solveur reproductible | Très bon signal, mais pas encore un théorème |
| `R(5,5)=43` | non prouvé | L'intervalle public reste `43 ≤ R(5,5) ≤ 46` |

Aucun de ces nouveaux commits ne change encore une borne Ramsey publiée.
Le résultat 54/54 reproduit une partie d'un résultat mathématique déjà connu,
`R(4,5) ≤ 25`, mais il est nouveau et utile pour notre propre chaîne
Lean/LRAT.

## Ce que le checkpoint des compteurs apporte

Le gros fichier SAT de la feuille `d=20,c=10,t0` contenait un bloc de
compteurs auparavant traité comme une donnée externe. Lean sait maintenant :

- générer les 84 compteurs ;
- compter exactement 690 ou 708 auxiliaires par compteur selon la borne ;
- placer les 58 716 auxiliaires sur les variables `903..59618` ;
- obtenir exactement 116 928 clauses ;
- vérifier l'égalité clause par clause avec le bloc du CNF certifié.

Le théorème générique prouve aussi que le témoin par comptes de préfixes
satisfait tout compteur de Sinz de borne positive. Le raccord final entre les
bornes de degrés du graphe et l'affectation partagée des variables auxiliaires
reste à écrire.

## Ce que le pilote degré 8 apporte

Le script fixe une racine de degré rouge 8 et utilise 27 parents du catalogue
`R(3,5,8)` avec 2 graphes `R(4,4,16)`, soit 54 feuilles. Il vérifie avant
le solveur :

- la formule fixe exacte ;
- le changement de convention de couleurs HOL4 vers Lean ;
- les 576 indices d'arêtes ;
- les 54 cubes ;
- les 179 enfants `R(3,5,8)` et les 2 enfants `R(4,4,16)`.

Résultats CaDiCaL 2.1.2 :

- 41/54 UNSAT sous 200 000 conflits ;
- 53/54 UNSAT sous 1 000 000 conflits ;
- dernière feuille UNSAT à 2 453 795 conflits ;
- résultat combiné : 54 UNSAT, 0 SAT, 0 UNKNOWN, 0 timeout.

Rapport détaillé :
`docs/R45_D8_54_PILOT_2026-08-06.md`.

## Verrou exact restant pour le degré 8

Trois obligations principales manquent avant d'écrire « preuve » :

1. des traces LRAT pour les 53 feuilles restantes, chacune rejouée par
   LRATCatcher ;
2. un théorème de complétude de la couverture droite `gen4416` ;
3. le transport des deux isomorphismes locaux en une permutation qui préserve
   les blocs, puis le raccord aux unités des feuilles.

La couverture gauche est maintenant certifiée par
`every_r35_order_eight_graph_enters_gen358` : tout graphe valide d'ordre 8
entre, à isomorphisme près, dans l'un des 27 parents, via une table de 179
témoins vérifiée par Lean. Le raccord du voisinage induit de `K25` à ce
théorème et le relèvement de sa permutation appartiennent encore au point 3.

La couverture droite est le vrai verrou. `gen4416` contient exactement les
deux graphes connus à 16 sommets, mais ce petit fichier de 312 octets n'est pas
une preuve autonome qu'il n'en existe aucun autre. L'audit du dépôt HOL4 n'a
trouvé ni export OpenTheory, ni LRAT, ni théorie compilée publiée. La
reconstruction officielle complète est annoncée avec un besoin pouvant
atteindre environ 500 Go de RAM.

La voie courte identifiée consiste à certifier d'abord la transition des 640
graphes d'ordre 15 vers les 2 graphes d'ordre 16, puis à traiter la complétude
d'ordre 15 séparément, ou à obtenir des auteurs un export de la preuve HOL4.

## Ordre de travail recommandé

1. **Terminé :** générer et rejouer dans Lean le LRAT d'une petite feuille
   degré 8 afin de valider l'interface.
2. **Terminé :** formaliser la couverture gauche `gen358` grâce au catalogue
   `R(3,5,8)` certifié.
3. **Prochaine étape :** choisir la stratégie de couverture droite :
   traduction HOL4, certificat
   d'énumération propre, ou export demandé aux auteurs.
4. Formaliser le raccord du voisinage d'ordre 8 et la permutation des blocs.
5. Produire et rejouer les 53 LRAT restants.
6. Répéter ensuite pour les degrés 10 et 12.
7. En parallèle, terminer le témoin auxiliaire partagé du bloc des 116 928
   clauses pour la branche `R(5,5)`.

Ne jamais annoncer une avancée mondiale ou `R(5,5)=43` avant la composition
Lean finale.
