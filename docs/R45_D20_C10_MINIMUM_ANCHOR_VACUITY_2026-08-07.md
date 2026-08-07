# Vacuité de la strate minimum-anchor `d20,c10`

Date : 2026-08-07.

## Résultat

Dans le découpage serré, `c` est le degré rouge interne de l'ancre choisie
de degré minimal dans le voisinage rouge `G` du sommet racine. Pour `d=20`,
la strate `c=10` est vide. Les 313 types historiques `r35_10` n'ont donc pas
à être résolus individuellement lorsque la condition minimum-anchor est bien
présente.

Le nouveau nombre de branches structurelles est :

- `K43` : `1509 - 313 = 1196` ;
- `K45` : `1815 - 313 = 1502`.

Les manifestes, résultats SAT et ponts Lean historiques ne sont pas modifiés
par ce checkpoint.

## Preuve

Soit `G` un graphe de `R(4,5,20)` et supposons que l'ancre minimale ait degré
interne `c=10`. Alors `delta(G)=10`, et la poignée de main donne

```text
2 e(G) = somme_v deg_G(v) >= 20 * 10 = 200,
```

donc `e(G) >= 100`. La classification publiée donne `E(4,5,20)=100`. Il faut
donc avoir `e(G)=100`, et l'égalité dans la somme impose que `G` soit
10-régulier.

La même classification donne une unique classe à 100 arêtes. Son représentant
officiel a la séquence de degrés

```text
9^2, 10^16, 11^2,
```

et n'est donc pas 10-régulier. Contradiction. On obtient en fait le lemme
local plus fort

```text
G dans R(4,5,20)  implique  delta(G) <= 9.
```

Cette conclusion concerne l'ancre **minimale**. Elle serait fausse pour une
ancre arbitraire : le représentant extrémal possède précisément seize sommets
de degré 10.

## Provenance byte-à-byte

- archive officielle :
  `https://users.cecs.anu.edu.au/~bdm/data/r45extreme.tar.gz` ;
- taille de l'archive : `90 599 728` octets ;
- SHA-256 de l'archive :
  `9CFAC9DBD1C209CFA342E5D5424DF2A7A3FBB008CA00BF0A992E5BBE72F925B6` ;
- membre : `r45extreme/r4520.100.g6` ;
- fichier local : `r55/r4520.100.g6`, 34 octets ;
- SHA-256 du fichier :
  `D1D1FF46BD5D153B51D7DA094F6BF459BCEAEFDA65EB4941EAD0BB9B09C897CD`.

Le vérificateur `r55/r45_d20_c10_vacuity.py` utilise uniquement la bibliothèque
standard et les primitives de `r55/ramsey.py`. Il contrôle :

- la taille et le SHA-256 du fichier ;
- l'unique record graph6 ;
- 20 sommets et 100 arêtes ;
- la séquence de degrés exacte ;
- l'absence de `K4` et d'ensemble indépendant de taille 5 ;
- la déduction minimum-anchor ;
- les tailles locales des catalogues `r35_0` à `r35_10` et les deux nouveaux
  totaux de branches.

Depuis la racine du dépôt :

```powershell
python -B r55/r45_d20_c10_vacuity.py
python -B -m unittest discover -s r55 -p "test_r45_d20_c10_vacuity.py"
```

## Limites de confiance

Le vérificateur authentifie et contrôle intégralement le représentant fourni.
Il ne reproduit pas l'énumération exhaustive qui établit les deux faits publiés
`E(4,5,20)=100` et `N(100)=1`. La vacuité est donc une conséquence vérifiée de
ces deux entrées de classification, et non encore un certificat autonome de
leur exhaustivité.

Il ne s'agit pas encore d'un théorème Lean. Pour une clôture formelle complète,
il faudra soit formaliser une hypothèse de classification explicitement citée,
soit importer un certificat d'exhaustivité contrôlable indépendamment.
