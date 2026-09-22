# Quotient K45 par motifs du bloc exclusif R(4,4)

Date : 2026-08-07.

## Lemme local exact

Soit `F` une coloration rouge/bleu sans `K5` monochromatique et `ra` une
arête de couleur `χ`. Posons

\[
C=N_χ(r)\cap N_χ(a),\qquad
A=N_χ(r)\setminus(C\cup\{a\}).
\]

Alors

\[
|A|=d_χ(r)-1-|C|,
\qquad F_χ[A]\in\mathcal R(4,4;|A|).
\]

En effet, un `K4` de couleur `χ` dans `A`, avec `r`, donnerait un `K5` de
couleur `χ`. Un `K4` de l'autre couleur, avec `a`, donnerait un `K5` de cette
autre couleur, car chaque sommet de `A` est relié à `a` dans cette couleur.
La minimalité de l'ancre n'intervient pas dans ce lemme; elle intervient dans
le schéma global de branches.

Ce maillon local est maintenant formalisé dans
`LRATCatcher.Tests.R55ExclusiveBlockR44`. Le théorème
`redEdge_exclusiveBlock_isRamseyFree` conclut exactement
`isRamseyFree 4 4 4` pour toute injection de quatre sommets du bloc. Build et
contrôle d'axiomes passent sans `sorry` ni `admit`; ce seul lemme est niveau 4.

## Arithmétique du quotient K45

Après élimination de la strate `d20,c10`, les 1 502 types minimum-anchor sont

```text
d20, c=2..9 ; d22, c=4..10.
```

Avec `q=d-1-c`, les douze strates `q>=12` contiennent 720 anciens types
`R(3,5,c)` :

```text
d20,c=2..7 : 2+3+7+13+32+71       = 128
d22,c=4..9 : 7+13+32+71+179+290   = 592
```

Le branchement proposé choisit une occurrence induite d'un motif dans `A` et
la normalise par une permutation interne à `A`. Il **remplace** le branchement
sur le type complet de `C`; il ne s'y multiplie pas. Le bloc `C` reste non
typé et les 21 arêtes/non-arêtes du motif sont fixées.

Le cover5 suivi d'ordre 12 donne cinq obligations par strate, donc 60 pour
`q>=12`. Les strates restantes sont

```text
q=11 : d20,c8 et d22,c10, multiplicité 2 ;
q=10 : d20,c9, multiplicité 1.
```

## Pilote catalogue R(4,4;10/11)

Les trois sources officielles ANU ont été gelées :

| source | records | octets compressés | SHA-256 |
|---|---:|---:|---|
| `r44_7.g6` | 362 | 2 172 | `6A3DA7F0687C392420F190DB0643B5C5B7ECB1A3C5ED098C7D96200185A5F010` |
| `r44_10.g6.gz` | 103 706 | 443 274 | `C34980E1CE734573D3A92486C6071144E154EE53E049B0E050CB1F8FFE0F6691` |
| `r44_11.g6.gz` | 546 356 | 2 605 345 | `05EEC90C5C14659E31F5E2C31A810B75649BA7D670D01A079ED9AABF17A3BBBC` |

Premier écran :

| ordre | trous cover5 | trous cover6 |
|---:|---:|---:|
| 10 | 13 494 | 8 022 |
| 11 | 2 137 | 778 |

Les familles existantes ne couvrent donc pas seules les petits ordres. Une
classification des trous parmi les 362 classes d'ordre 7, suivie d'un cover
glouton déterministe, fournit toutefois :

| ordre | famille individuelle | famille fermée par complément |
|---:|---:|---:|
| 10 | 24 motifs | 13 paires = 26 motifs |
| 11 | 14 motifs | 7 paires = 14 motifs |

Le manifeste suivi donne tous les graph6 explicitement. Un second programme,
sans import du générateur, utilise une représentation par lignes d'adjacence,
reconstruit les orbites étiquetées, revérifie chaque record comme `R(4,4)`,
contrôle la fermeture par complément et rescane tous les 7-sous-ensembles.
Résultat : 103 706/103 706 et 546 356/546 356, zéro trou.

La compression d'architecture obtenue sur le catalogue gelé est donc

\[
12\cdot5+2\cdot14+24=\boxed{112}
\]

obligations individuelles, ou, si la fermeture par complément est exigée,

\[
12\cdot6+2\cdot14+26=\boxed{126}.
\]

Ce sont des obligations motif-conditionnées, pas des branches SAT fermées.

## Artefacts et reproduction

- module Lean du lemme exclusif :
  `vendor/lrat-catcher/LRATCatcher/Tests/R55ExclusiveBlockR44.lean`,
  16 147 octets, SHA-256
  `81CCC640191ADFBBC9EC1F651454A8D3908A20C7FCFEAA1D6E218CF9BD2B1A7E` ;
- manifeste suivi :
  `scripts/r45_d12_cover9_universal/R44_SMALL_ORDER_MOTIF_COVERS_2026-08-07.json`,
  SHA-256
  `C17EA950F1E02AAF1223AA9E230208498D2ADC7AAA7077A488435D371FE8B614` ;
- rapport premier écran sur `S:` : 11 502 octets, SHA-256
  `D8701ACA0D1B5EC77EDED32924DA42E89D6FE9126D474340375B620748897B00` ;
- rapport glouton sur `S:` : 12 443 octets, SHA-256
  `BDA31C3B2346B06CF85311C11C5E1A2CBC338E79D5C01E634FA1F5999CED2268` ;
- rejeu indépendant final sur `S:` : 1 366 octets, SHA-256
  `B85E57FA3D7D25A901DD98E387264B8B47FB6CC71F8721FA7CD07BD7DC1E3203`.

Les trois passes utiles ont pris respectivement 88,20 s, 105,97 s et 70,65 s, avec
un seul processus. Les catalogues et rapports restent sur `S:`.

## Frontière de confiance et importance

Les nouvelles couvertures sont classées **niveau 1** : observation exhaustive
et indépendamment rejouée sur des catalogues officiels gelés. Le lemme local
du bloc exclusif est séparément niveau 4. Ne sont pas établis ici :

1. la complétude des catalogues dans Lean ou par certificat local ;
2. un théorème universel remplaçant cette dépendance aux catalogues ;
3. le pont formel du bloc exclusif vers les formules K45 ;
4. la compatibilité avec `rooted_signature_lex_encoding` — en l'état, ce
   briseur peut empêcher de placer le motif sur les sept premiers sommets ;
5. un gain de propagation ou de temps SAT ;
6. la fermeture d'une seule obligation, et donc toute nouvelle borne.

Nouveauté probable : **utile**, sous forme d'une architecture de branchement
compacte et certifiable. Importance mathématique actuelle : locale. Proximité
d'une publication ou de `R(5,5)<=45` : faible tant qu'un pilote SAT
motif-conditionné n'a pas fermé de famille. Les cinq motifs testés auparavant
sur une feuille globale étaient restés `UNKNOWN`; une réduction du nombre de
feuilles ne garantit donc pas une réduction du coût.

La prochaine expérience rationnelle est une seule obligation représentative,
sans `signature_lex`, plafonnée à 60 s/100 000 conflits/1 Gio. Elle ne doit être
étendue que si elle améliore au moins d'un facteur deux la propagation ou le
temps face au branchement typé correspondant.

## Autres pistes auditées, non promues

`DLS13` conjecture que, pour les deux blocs exclusifs `A,D` d'une arête,
`min(|A|,|D|)<=13`. Les 328 graphes K42 connus et leurs compléments ne donnent
aucune violation, mais la source ANU dit explicitement que cette liste n'est
pas exhaustive. DLS13 reste niveau 0 et n'éliminerait que 45 des 1 502 types
K45; ce n'est pas la piste principale.

Une coupure additive candidate vient du double comptage. Pour une racine `r`,
`A=N(r)`, `B=V\(A∪{r})` et `S_w=N(w)∩A`, la borne `R(3,4)=9` donne

\[
\sum_{w\in B} e(F[S_w])\le 8e(F[A]).
\]

Sa projection par les minima d'arêtes des graphes `R(4,5;s)` pourrait fournir
une contrainte PB/ILP, mais elle n'a fermé aucun profil et n'est ni formalisée
ni revue : niveau 0 dans la grille du projet.

Enfin, dans la strate K45 `d20,c2`, les deux blocs exclusifs ont exactement 17
sommets; sous l'unicité officielle de `R(4,4;17)`, ils sont tous deux dans
l'unique classe publiée et le bloc restant a taille 7. Cette réduction
Paley--Paley est correcte conditionnellement à la classification, mais aucune
obstruction globale n'en a encore été tirée.

Sources primaires : catalogue [ANU Ramsey graphs](https://users.cecs.anu.edu.au/~bdm/data/ramsey.html),
[R(5,5)<=46](https://arxiv.org/abs/2409.15709), et
[A Formal Proof of R(4,5)=25](https://doi.org/10.4230/LIPIcs.ITP.2024.16).
