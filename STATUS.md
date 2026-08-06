# Projet R(5,5) — état vérifiable

Date de l’audit : 6 août 2026.

## Résultat public et cible

L’état public vérifié reste

\[
43 \le R(5,5) \le 46.
\]

La borne inférieure vient de graphes à 42 sommets sans clique ni ensemble
indépendant de taille 5. La borne supérieure 46 a été publiée en 2024.
La cible exacte est de décider s’il existe un tel graphe à 43 sommets :

- un modèle SAT vérifié prouverait `R(5,5) ≥ 44` ;
- une réfutation complète formellement reliée au problème prouverait
  `R(5,5) = 43`.

Nous n’avons pas encore obtenu cette décision globale.

## Jalons effectivement vérifiés

### Encodage et borne inférieure

- CNF Ramsey canonique de `K_43` : 903 variables et 1 925 196 clauses de
  largeur 10.
- SHA-256 de cette CNF :
  `B2E3A560E6F77EBDA6D1D41C01469738E672701CDAD0E1E98C0557CB88D38C42`.
- Les 328 graphes officiels à 42 sommets et leurs compléments ont été audités.
- Un témoin officiel à 42 sommets est vérifié dans Lean, donnant formellement
  `R(5,5) ≥ 43`.
- Une preuve LRAT fraîche de `R(3,3) ≤ 6` a été rejouée dans Lean pour valider
  la chaîne solveur → certificat → vérificateur formel.

### Petites bornes Ramsey et borne globale de degrés

- `R(3,4) ≤ 9` est maintenant certifié par un LRAT complet de 961 008 octets
  produit depuis l'encodeur Lean : 36 variables, 210 clauses, 8 937 conflits.
- `RamseyRecurrence.lean` formalise la partition des 17 arêtes incidentes à un
  sommet, la restriction à neuf voisins et le complément bleu. Avec le
  certificat précédent, `r44_upper` prouve `R(4,4) ≤ 18`.
- `R55DegreeBounds.lean` prouve conditionnellement que `R(4,5) ≤ 25` implique
  que chaque sommet d'une hypothétique coloration `K43` sans `K5`
  monochromatique a ses deux degrés, rouge et bleu, au plus égaux à 24.

Le certificat `R(4,5) ≤ 25` reste à produire. Son CNF Lean exact a 300
variables et 65 780 clauses. Une recherche monolithique reste `UNKNOWN` après
5 000 000 conflits ; avec LRAT, un million de conflits produisait déjà
448 054 388 octets sans clause vide. Les mesures complètes sont dans
`RAMSEY_BOUND_DIAGNOSTICS.md`. La prochaine tentative doit donc employer une
réduction par symétrie ou une couverture de cubes vérifiée.

### Pilote `R(4,5,25)`, degré racine 8

Le pilote réduit la formule à 54 feuilles (`27 × 2`) et CaDiCaL les a toutes
signalées UNSAT. Ce résultat solveur reste expérimental tant que toute la
couverture et toutes les traces ne sont pas composées dans Lean.

Lean certifie maintenant la feuille `d8_l22_r01` dans
`R45DegreeEightPilot` :

- CNF de 1 982 968 octets, SHA-256
  `F2E1D012DEA5911F9F4D9F7B50641CA483ECE5F65B1F666E92BE61CF332AFEAF` ;
- LRAT de 8 352 876 octets, SHA-256
  `3EB38EFAEBDDE8E4B2EF0FD78B1AC5C6B449FC8E1A1D814A94511081290E9023`.

`R45DegreeEightCover` certifie aussi la couverture gauche : une table relie
les 179 représentants du catalogue exhaustif `R(3,5,8)` aux 27 parents
`gen358` et prouve que tout graphe valide d'ordre 8 admet une complétion
isomorphe entrant dans un parent concret.

Restent la couverture exhaustive droite `gen4416`, le transport des
isomorphismes en une permutation de `K25` qui préserve les deux blocs, et les
53 traces LRAT non encore rejouées.

### Réduction structurelle

Les cas racines utiles sont `d=18` et `d=20`. En choisissant, dans le
voisinage de la racine, un sommet de degré interne minimal et en utilisant les
bounds extrémales de `R(4,5,18)` et `R(4,5,20)`, le manifeste serré contient
1 509 branches :

- 599 branches `d=18`, codégrés `c=0..9` ;
- 910 branches `d=20`, codégrés `c=2..10`.

SHA-256 du manifeste :
`6480F59552D21446BE448DC50CC85395BB711746193848E3291164CADEFE9E26`.

### Strate `d=20,c=10`

Les 313 types du catalogue `R(3,5,10)` ont tous été éliminés côté recherche :

- 308 types UNSAT à 100 000 conflits ;
- quatre survivants supplémentaires UNSAT avant 1 000 000 conflits ;
- le dernier type, `t312`, est le graphe de couronne
  `W5 = C5[\overline{K_2}]`, de groupe d’automorphismes
  `C2^5 ⋊ D5` d’ordre 320.

Pour `t312`, CaDiCaL termine UNSAT en 186 702 conflits. Sa formule corrigée
ne contient aucune tautologie ni aucun littéral répété dans une clause :

- 63 080 variables ;
- 2 049 737 clauses ;
- CNF SHA-256 :
  `2263EB489E72CF2AA3688F554FD3301590094B09880200A842ACBEB308AB880F` ;
- LRAT SHA-256 :
  `B82FE815F61F28AC474F52D79448B760AECF72A377B9E2AD21AA98059A7A1688`.

Le diagnostic Lean rejoue les 1 383 611 actions utiles jusqu’au succès. Le
théorème `r55_d20_c10_t312_w5_unsat` compile avec `lrat_reflect`. Ce théorème
porte exactement sur la CNF externe renforcée ; il ne constitue pas encore à
lui seul une preuve du cas mathématique non étiqueté.

Le mode utilisé est le mode natif de LRAT-Catcher. Sa base de confiance est le
noyau Lean plus le compilateur, comme `native_decide`; `#print axioms` expose
explicitement ce pont natif. Un rejeu `+kernel` éliminerait cette confiance
additionnelle, mais serait beaucoup plus coûteux sur ce certificat.

### Exhaustivité des catalogues `R(3,5,n)`, `n≤10`

Un nouveau certificat par extensions d’un sommet couvre :

- 912 graphes de catalogue ;
- 206 003 voisinages candidats réénumérés par le vérificateur ;
- 8 989 extensions valides ;
- une permutation explicite, vérifiée arête par arête, pour chaque extension.

Le certificat JSON fait 283 422 octets, SHA-256
`47B9E29AD80093CE527B75369303E32778642B0986F114EE22B35FE7BF7A8891`.

Le module Lean `r35_catalogue_extensions_checked` vérifie indépendamment :

- l’absence de triangle et d’ensemble indépendant de taille 5 ;
- la bonne formation et la symétrie de chaque graphe ;
- tous les masques d’extension ;
- toutes les permutations vers le catalogue suivant.

Le build Lean des données, du certificat et du contrôle W5 réussit. La chaîne
sémantique est maintenant entièrement instanciée :

- décomposition canonique par suppression du dernier sommet ;
- validité du parent et du masque ;
- transport du masque par une permutation finie forte ;
- invariance de `validGraph` par isomorphisme ;
- transition vers un représentant certifié et composition des isomorphismes.

Le théorème Lean `r35_catalogues_complete` prouve l’exhaustivité de chaque
niveau enregistré, et `r35_catalogue_order_ten_complete` celle du catalogue
`R(3,5,10)`. Le module d’intégration `R35CatalogCheckpoint.lean` compile.

### Symétrie W5

Le module Lean `w5_signature_symmetry_checked` vérifie :

- les 320 permutations distinctes ;
- qu’elles préservent toutes `W5` ;
- les 1 024 signatures binaires possibles ;
- exactement 39 orbites de signatures ;
- que les clauses choisissent exactement le minimum de chaque orbite ;
- que toute orbite contient une signature acceptée.

### Pont local degré 20 / codegré 10

`R55CommonNeighborhoodBridge.lean` prouve désormais qu'un voisinage rouge
commun exact de taille 10 dans une coloration `K5/K5`-libre ne contient ni
triangle rouge ni ensemble bleu de taille 5, puis applique
`r35_catalogue_order_ten_complete` pour obtenir un représentant certifié.

Le constructeur canonique `LocalD20C10Witness.package` part seulement des
trois faits locaux `degree(root)=20`, `anchor ∈ N(root)` et
`codegree(root,anchor)=10`. Il construit en Lean les listes exactes, le graphe
induit empaqueté et toutes les obligations de bonne formation. Le théorème
`LocalD20C10Witness.covered_by_orderTenCatalogue` ferme ensuite la couverture
sémantique locale. Aucun `sorry`, `admit` ou nouvel axiome explicite.

La spécialisation `LocalD20C10Witness.ofCanonicalBranch` construit ce témoin
depuis les deux égalités de listes correspondant exactement au label SAT
canonique, et `canonicalBranch_covered_by_orderTenCatalogue` compose ce
constructeur avec la couverture.

Ce raccord est maintenant prouvé dans `R55CanonicalUnitsBridge.lean` : les 42
unités racine et 19 unités ancre sont reproduites exactement, leur satisfaction
donne les deux listes canoniques, puis
`CanonicalD20C10Units.covered_by_orderTenCatalogue` atteint le catalogue.
L'audit indépendant a comparé les 61 littéraux Python et Lean, leurs polarités
et indices, sans écart. Le prochain raccord concerne les unités de type
`fixed_anchor_type_clauses`, puis la réduction WLOG qui produit les unités
canoniques depuis une branche arbitraire.

Depuis, `R55TypedUnitsBridge.lean` traite exactement les 45 unités de type et
`R55ColoringPermutation.lean` prouve l'invariance Ramsey sous toute permutation
des 43 sommets. Enfin `R55CanonicalRelabeling.lean` construit, depuis un témoin
local degré 20/codegré 10, une permutation globale, une coloration réétiquetée
toujours Ramsey-libre et les 61 unités canoniques. Il reste à obtenir ces
témoins locaux dans la couverture globale de toutes les branches et à relier
les formules renforcées/LRAT.

Pour la feuille `t0`, `R55MinLeafBridge.lean` et
`R55MinLeafSemantics.lean` isolent exactement la formule certifiée :
1 925 196 clauses Ramsey, 116 928 clauses de compteur de degrés, 5 149 clauses
de minimum interne et 106 unités canoniques/type. Le théorème terminal obtient
une contradiction sous satisfaction explicite des deux blocs compteurs. Leur
soundness est donc le résidu précis ; elle n'est pas supposée implicitement.

## Ce qui manque avant toute annonce de `R(5,5)=43`

1. Produire `LocalD20C10Witness` depuis les hypothèses globales/de branche et
   étendre cette réduction aux autres valeurs de degré/codegré des 1 509
   branches du problème `K43`.
2. Relier les contraintes auxiliaires au graphe : complétude des compteurs de
   cardinalité, comparateurs lexicographiques et régularité.
3. Certifier `R(4,5) ≤ 25`, puis instancier la borne globale de degrés déjà
   formalisée et couvrir les cas racines utilisés pour choisir l’ancrage
   minimal.
4. Produire puis rejouer les certificats UNSAT pour toutes les feuilles, pas
   seulement les deux feuilles déjà importées.
5. Composer ces résultats en un théorème final sur le prédicat Ramsey, puis
   seulement conclure avec le témoin à 42 sommets.

Une architecture compacte évite de stocker 313 copies de la CNF : une base
canonique partagée avec bits de sélection et un code préfixe complet de 313
feuilles. Les preuves LRAT resteraient autonomes par feuille, tandis que Lean
composerait les feuilles avec un certificat de couverture.

## Reproductibilité locale

Fichiers principaux :

- `work/r55/ramsey.py` — encodages et générateurs déterministes ;
- `work/r55/catalog_certificate.py` — génération et vérification indépendante
  du certificat d’extensions ;
- `work/r55/r35_extension_certificate.json` — certificat des catalogues ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogCertificate.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogCompletenessCore.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogCompleteness.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R35CatalogCheckpoint.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R55W5Symmetry.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R55Branch.lean`.

La suite locale contient 37 tests Python, tous réussis.

## Sources publiques

- Catalogue Ramsey de Brendan McKay :
  https://users.cecs.anu.edu.au/~bdm/data/ramsey.html
- Borne supérieure `R(5,5) ≤ 46` :
  https://arxiv.org/abs/2409.15709
- LRAT-Catcher :
  https://github.com/leansolving/lrat-catcher
