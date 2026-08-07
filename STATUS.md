# Projet R(5,5) — état vérifiable

## Mise a jour de recherche - fin du 7 aout 2026

Cette section remplace les compteurs 7/13 et 1 509 encore presents plus
bas comme historique du checkpoint precedent.

### Cover6 universel, degre 8

Les 13 CNF residuelles a deux centres sont maintenant presentes sur S:,
rehachees et parsees. Chaque formule contient exactement les 21 unites
attendues. Ensemble, elles totalisent 19 657 663 clauses et
1 077 652 051 octets. Le manifeste externe a pour SHA-256
DDAF42888C6A77C432EC9AA4799D6A24EEDB2088AA25C97C251A82D3986DFB8C.

CaDiCaL 2.1.2 a rendu UNSAT_WITHOUT_PROOF sur 13/13 cas, avec 58 a 3 073
conflits et 9 889 conflits cumules. Le manifeste du batch a pour SHA-256
AA5E11028D9B8A228E2F6EB7E5F11D0C740BBFDEED9315134C3F1DED8BB1E492.
Aucun LRAT n'a ete demande. Ce resultat ferme l'ecran solveur, pas encore le
theoreme universel. L'audit a precise une lacune anterieurement sous-estimee :
le verificateur ne regenere pas encore clause par clause la grosse formule,
et ne reconstruit pas independamment sa simplification vers les 13
residuelles. Restent donc d'abord ce pont semantique exact, puis seulement les
LRAT, leurs replays et la composition avec les branches a deux centres.

Une chaine jouet ferme maintenant la methode sur K5 : toute coloration sans
triangle monochromatique contient un P3 positif induit. Les 80 clauses sont
reconstruites declarativement, la semantique des deux composants est verifiee
sur les 1 024 affectations, le LRAT est rejoue par Lean et le theoreme terminal
compile. Des mutants controlent polarites, indexation, preuve et cas crucial
d'une mauvaise formule rendue trivialement UNSAT, rejetee avant tout replay;
ainsi un certificat valide eventuel ne pourrait pas masquer l'erreur
d'encodage. Niveau 4 pour ce jouet uniquement; aucune conclusion cover6-d8 ou
R(5,5) n'en decoule. Le rejeu Lean est force hors cache par `lake env lean`.
Voir
docs/R44_COVER6_D8_SEMANTIC_TARGET_2026-08-07.md.

### Lemme extremal minimum-anchor

Dans le schema serre, c est le degre interne minimal du voisinage racine G.
Pour d=20,c=10, la poignee de main impose e(G)>=100; la classification
officielle actuelle donne E(4,5,20)=100, donc G devrait etre 10-regulier.
L'unique classe d'isomorphisme officielle au niveau 100, authentifiee par le
record SHA-256
D1D1FF46BD5D153B51D7DA094F6BF459BCEAEFDA65EB4941EAD0BB9B09C897CD,
a pourtant les degres 9^2 10^16 11^2. La strate minimum-anchor est vide.

Le gain exact est de 313 types : le probleme K43 passe de 1 509 a 1 196
branches non vacues; le squelette K45 de 1 815 a 1 502. Cette conclusion
depend de l'exhaustivite publiee par le catalogue ANU mis a jour; le papier de
1995 seul ne donnait pas encore l'egalite E=100.

### Ecrans K43 et K45

Huit feuilles representatives K43 ont ete testees avec ancre minimale
specialisee, ordre lexicographique des signatures, 100 000 conflits et
1 000 Mio par processus. d18_c9_t195 est UNSAT sans LRAT en 95 conflits;
les sept autres sont UNKNOWN a la limite, en 35,19--54,76 s de solveur. Les
CNF ont ete supprimees. Journal externe : 55 466 octets, SHA-256
4B8F4F8ED8A7A937AA0127FB7732F375202E68CDF818EAA6F3EF1D511074A5C6.

Pour K45, parite et complementation reduisent une racine paire a d=20 ou
d=22. Apres le lemme precedent, le schema type contient 1 502 branches.
L'identite d'exces donne
sum Delta = 6(n20+n24) + 15/2(n21+n23) + 8n22, mais les seules bornes
extremales e/E n'eliminent aucun degre : les 106 076 distributions de degres
compatibles avec la parite restent faisables dans cette relaxation. Elle
force toutefois au moins 18 des 90 voisinages orientes a deficit au plus 4;
hors du cas 22-regulier, un deficit au plus 3 existe. Une generation CNF K45
brute a ete arretee a 114 449 417 octets partiels puis entierement nettoyee :
la prochaine etape doit exploiter la structure, pas produire les 1 502
grosses formules.

### Quotient K45 par bloc exclusif R(4,4)

Pour une arete racine-ancre de couleur chi, le bloc des voisins chi de la
racine qui sont non-voisins chi de l'ancre est un graphe R(4,4) de taille
q=d-1-c. Cette observation permet de remplacer le type complet R(3,5,c) par
une occurrence induite d'un petit motif, en laissant C non type.
Le lemme local est formalise dans
`R55ExclusiveBlockR44.redEdge_exclusiveBlock_isRamseyFree`, qui conclut le
predicat standard `isRamseyFree 4 4 4`; ce maillon seul est niveau 4.

Des copies locales gelees des catalogues officiels R(4,4;10) et R(4,4;11)
ont ete scannees puis rejouees par une seconde implementation sans import du
generateur. Les familles explicites couvrent 103 706/103 706 et
546 356/546 356 records; chaque record a aussi ete revalide R(4,4). Avec le
cover5 d'ordre 12 et la vacuite d20,c10, la voie hybride catalogue-relative
compte 112 obligations motif-conditionnees au lieu de 1 502 types; une version
fermee par complement en compte 126.

Covers et quotient restent niveau 1 et non une fermeture : la completude et
la provenance des catalogues ne sont pas reliees a Lean, le pont K45 n'existe
pas, `signature_lex` peut entrer en conflit avec la normalisation du motif, et
aucun gain SAT n'est mesure. Voir
docs/R45_EXCLUSIVE_R44_MOTIF_QUOTIENT_2026-08-07.md et le manifeste
scripts/r45_d12_cover9_universal/R44_SMALL_ORDER_MOTIF_COVERS_2026-08-07.json.
Manifeste SHA-256 :
C17EA950F1E02AAF1223AA9E230208498D2ADC7AAA7077A488435D371FE8B614;
rejeu final externe SHA-256 :
B85E57FA3D7D25A901DD98E387264B8B47FB6CC71F8721FA7CD07BD7DC1E3203.

### Evaluation scientifique

L'intervalle public reste 43 <= R(5,5) <= 46; aucune nouvelle borne n'est
obtenue. La fermeture solveur 13/13 de cover6-d8 rapproche un lemme
computationnel publiable, mais il manque la certification LRAT/Lean. La
vacuite d20,c10 est une simplification de preuve importante, probablement
implicite dans les donnees publiees plutot qu'une nouveaute mathematique
majeure. L'ecran K43 montre qu'une percee demandera un nouveau split pour les
petites codegrees, pas seulement davantage de conflits.

Date de l’audit : 7 août 2026.

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

## Point de recherche vérifié — branche de degré 12

La branche de degré rouge 12 de `R(4,5,25)` possède un échafaudage
sémantique Lean compilé : partition `1+12+12`, sélection exhaustive des 12
types `R(3,5,12)`, permutation globale de `Fin 25`, 66 unités exactes du
bloc gauche et pont générique pour les motifs partiels du bloc droit. La
formule gardée compte 280 variables et 54 638 clauses. Ses quatre codes de
sélecteur invalides sont certifiés, mais **aucun des 12 cas mathématiques
globaux n’est encore fermé**.

Deux résultats structurels nouveaux changent toutefois nettement la qualité
de la piste.

Premièrement, la cible universelle `cover9`, indépendante du catalogue
d’ordre 12, est certifiée au niveau CNF exact pour toute la tranche de degré
racine 8. Les 13 cas à deux centres ont tous un LRAT CaDiCaL rejoué
indépendamment par LRAT-Catcher/Lean. Les preuves totalisent 222 740 623
octets et leur manifeste portable a pour SHA-256
`77FE47B5BC73865EDB0405DFC2D3B0A367C2A757B27A83CDC981D5958F80DE23`.
Lean formalise séparément une vraie permutation fixant la racine, les bornes
de degré, la normalisation du second centre, la disjonction exacte des 13 cas
et le transport de la liberté `R(4,4)` et des motifs induits. Il manque
encore le pont sémantique entre les CNF résiduelles générées et
`TwoCenterBranch`, puis la composition avec les 13 replays. Les degrés
racine 3 à 7 de `cover9` ne sont pas certifiés.

Deuxièmement, une recherche exacte trouve le minimum sous fermeture par
complément : **trois paires, donc six motifs d’ordre 7**, couvrent les
1 449 166 enregistrements du `r44_12.g6` officiel gelé. Les paires sont
`F@h^g`/`FKDhw`, ``FG`Xo``/`FdW}w` et `FHFLw`/`FIIXw`. Le
TSV a pour SHA-256
`404E49E3218424FCB73314ADEE42CC873CD3F8D67E4615653A8BC0210F61AD16`
et sa fermeture étiquetée de 25 200 masques a pour SHA-256
`04B9688924BFC2EF6F92FB5734B19E7E771C37446DD3E442ECED8648BE1CBDD7`.

La borne supérieure a été rejouée directement sur les 1 449 166 graphes, avec
792 sous-ensembles testés par graphe, sans lire la matrice d’incidence ni un
témoin : zéro trou en 167,14 s. La borne inférieure autonome reconstruit les
`2^21` graphes étiquetés d’ordre 7, les 923 012 graphes `R(4,4)`, les 181
paires de compléments et 23 760 sous-graphes induits d’un noyau explicite de
30 graphes `R(4,4,12)`. Elle exclut les 16 471 choix d’au plus deux paires.
Le noyau, deletion-irréductible, a pour SHA-256
`EB61306B5DA0F15DC1112D82007BB29CD2FD3AEE460FD1C0D62E24401C66C8CC`.
La borne inférieure est absolue sur ces graphes explicites ; l’upper reste
explicitement relatif au catalogue officiel gelé.

La fermeture par complément réduit la future preuve universelle aux degrés
représentatifs 6, 7 et 8. Deux implémentations indépendantes valident
exhaustivement 25 200 cubes locaux fermés par complément, de SHA-256
`0239E74AC009B28173E59C3293F7F9C9370A99832B19BB28205EF449E6238F7D`.
Les tailles calculées sont 4 858 890, 4 312 419 et 3 367 437 clauses.
L'ancienne formulation « CNF de degré 8 doublement vérifiée » était trop
forte. Le fichier gelé fait 189 298 232 octets, SHA-256
`64E411A23778972A85DE7C8613A1977F98115E2EC3C9B1711D129932A4ECBB5A`,
mais son vérificateur ne reconstruit ni chaque clause globale ni les
réductions vers les résiduelles.

Les 13/13 résiduelles à deux centres existent désormais, contiennent chacune
les 21 unités attendues et ont rendu UNSAT sans preuve. Leur provenance exacte
depuis la source reste à certifier et aucun LRAT cover6 n'existe. Il ne s'agit
donc pas d'un théorème UNSAT complet.

Le compteur global demeure donc **0/12 cas mathématiques de degré 12
fermés**. Aucune nouvelle borne de Ramsey n’est revendiquée. Le minimum
cover6 et la certification cover9 degré 8 sont des lemmes computationnels
potentiellement publiables, sous réserve d’un audit bibliographique plus large
et des compositions sémantiques manquantes. Le relais complet pour la
prochaine conversation est
`docs/NEXT_CONVERSATION_HANDOFF_2026-08-07.md`.

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

### Branche certifiée `R(4,5,25)`, degré racine 8

Le pilote à 54 couples (`27 × 2`) est maintenant fermé formellement. Une
formule maître gardée partage les blocs d'unités, et une couverture de 59 cubes
(54 codes admissibles plus cinq bloqueurs de codes invalides) a été rejouée
dans Lean. Le théorème terminal exclut toute racine de degré rouge 8 d'une
coloration `(4,5)`-libre de `K25`.

Le premier jalon historique, la feuille `d8_l22_r01`, reste certifié dans
`R45DegreeEightPilot` :

- CNF de 1 982 968 octets, SHA-256
  `F2E1D012DEA5911F9F4D9F7B50641CA483ECE5F65B1F666E92BE61CF332AFEAF` ;
- LRAT de 8 352 876 octets, SHA-256
  `3EB38EFAEBDDE8E4B2EF0FD78B1AC5C6B449FC8E1A1D814A94511081290E9023`.

La fermeture complète utilise désormais `R45DegreeEightGuardedMasterSemantics`
et `R45DegreeEightGuardedMaster` : la décomposition exacte a 282 variables et
55 926 clauses (`55 006 + 675 + 240 + 5`), son UNSAT implique les 54
contradictions admissibles, et `lrat_cover_reflect_trim` rejoue les 59 preuves
de feuilles ainsi que le certificat de couverture. Le build terminal a réussi
56/56 et `#print axioms` ne contient aucun `sorryAx`.
Les 59 LRAT et le certificat de couverture totalisent 2 405 113 598 octets
hors Git. Quatre archives ZIP64 totalisant 647 326 949 octets ont été créées
sur SSD, puis entièrement redécompressées et rehachées avec succès. Leurs
empreintes et l'outil `proof_bundle.py` sont versionnés; la portabilité publique
reste conditionnée au téléversement puis au retéléchargement des quatre assets
de la Release GitHub planifiée `r45-d8-guarded-master-lrat-v1`.

`R45DegreeEightCover` certifie aussi la couverture gauche : une table relie
les 179 représentants du catalogue exhaustif `R(3,5,8)` aux 27 parents
`gen358` et prouve que tout graphe valide d'ordre 8 admet une complétion
isomorphe entrant dans un parent concret.

`R45DegreeEightBridge` raccorde maintenant cette couverture à une vraie
branche de `K25`. Le théorème `degree_eight_local_split` envoie les huit
voisins rouges dans `gen358`, construit les seize voisins bleus, prouve que
leur coloration complémentée est `(4,4)`-libre, et formalise la relation avec
les couleurs brutes attendues par les unités DIMACS.

La stratégie droite retenue évite le catalogue géant `R(4,4,15)`.
`R44RootedR34Catalogue` certifie le filtrage des catalogues `R(3,5)` :
exactement 9 représentants `R(3,4,7)` et 3 représentants `R(3,4,8)`, complets
modulo `GraphIsoFin`. `gen4416_rooted_classifier.py` reconstruit ensuite les
27 paires, exactement 64 masques autorisés et un CNF gardé de 83 variables et
10 880 clauses. Son LRAT de 3 658 365 octets est rejoué dans Lean par
`r44_rooted_gen4416_classifier_unsat`.

La couverture sémantique qui manquait est maintenant composée. Le théorème
Lean terminal est :

```lean
ramseyFree_isomorphic_to_gen4416
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 16 4 4 coloring) :
    ∃ targetIndex,
      targetIndex < gen4416GraphIds.length ∧
        GraphIsomorphicFin (coloringGraph 16 coloring)
          (gen4416Graph targetIndex)
```

Il prouve donc que toute coloration `(4,4)`-libre de `K16` est fortement
isomorphe à l'une des deux cibles matérialisées dans `gen4416`. L'énoncé est
une couverture par ces deux cibles ; leur non-isomorphisme mutuel n'est pas
utilisé et n'est pas encore un théorème Lean séparé.

La chaîne certifiée est la suivante :

1. `R44RootedDegreeSplit` oriente, par complémentation éventuelle, une racine
   de degré 7 en n'utilisant que la borne certifiée `R(3,4) ≤ 9` ;
2. `R44RootedBlockCatalogues` place le voisinage d'ordre 7 et le complément de
   l'antivoisinage d'ordre 8 dans les catalogues exhaustifs de 9 et 3 types ;
3. `R44RootedMixedCNFSemantics` relie les quatre familles sémantiques de
   `K4`/ensembles indépendants mixtes au CNF gardé exact ;
4. le LRAT de `R44RootedGen4416Classifier` force l'une des 64 lignes
   autorisées ;
5. `R44RootedGen4416Cover` vérifie 64 permutations vers les cibles et deux
   permutations d'auto-complémentarité ;
6. `R44RootedCanonicalRelabeling` et `R44Gen4416Classification` composent les
   isomorphismes, désorientent le complément et concluent pour une coloration
   arbitraire.

`R44Gen4416TargetAudit` vérifie en outre que les deux cibles matérialisées sont
elles-mêmes `R(4,4)`-valides. Les artefacts centraux ont pour SHA-256 :

- CNF gardé :
  `863C78226DDEFE17FEEF046F7F818D01ECFE63EE96663AEFEC1BE81EC591AAF4` ;
- LRAT :
  `786578E2E05E62E5B814BFC86656513E42A52D6467B190783637D6FC1AD33A61` ;
- table des 64 lignes :
  `1995924E5D942F437BF24A649A23EC9843A9375678DA8A044ABAD4FBF05E4670` ;
- données Lean des 64 couvertures et 2 auto-compléments :
  `39A747796E2C3FE6FFB9CE2FDE541711A47487A035F4F0C7AB1981BA4243FAB3`.

Le nouveau module `R45DegreeEightGen4416Bridge` compose ensuite les deux
couvertures locales dans la branche globale. Le théorème compilé
`degree_eight_enters_gen358_and_gen4416` part d'une coloration `(4,5)`-libre
de `K25` et d'une racine de degré rouge 8, puis fournit simultanément un parent
`gen358` couvrant le bloc rouge et une cible `gen4416` fortement isomorphe au
bloc bleu complémenté. Son SHA-256 source est
`85B0DBF179D2DA759AA14D13E0834D788255E0B0F33003BDDD5937ABA4B031B5`.
Cette composition existentielle est donc fermée. La couche suivante est
maintenant matérialisée dans les sources :

- `R45DegreeEightGlobalPermutation` construit la permutation globale de `K25`
  qui fixe la racine et relabelle séparément les blocs de tailles 8 et 16 ;
- `R45DegreeEightRawGen4416Bridge` transporte la classification du bloc bleu
  complémenté vers ses couleurs ambiantes brutes ;
- `R45DegreeEightPilotSemantics` reconstruit exactement les 55 154 clauses de
  `d8_l22_r01` et isole les 148 unités de parents ;
- `R45DegreeEightReducedAssignment` établit les trois obligations sémantiques
  non unitaires de cette feuille pour la restriction canonique à `K24` ;
- `R45DegreeEightGen358UnitsBridge` extrait de la couverture gauche une
  permutation qui respecte chaque couleur fixée du parent `gen358` ;
- `R45DegreeEightGen4416UnitsBridge` extrait la permutation cible-vers-bloc
  brut et prouve la satisfaction littérale de toutes les unités droites
  décalées ;
- `R45DegreeEightLeafAssemblyCore` factorise la permutation globale et les
  deux blocs d'unités pour tout couple admissible d'indices de parents ;
- `R45DegreeEightBranchComposition` définit l'interface certificative unique
  `AllAdmissibleDegreeEightPairsContradictory` et prouve qu'elle exclut toute
  racine de degré rouge 8 ;
- `R45DegreeEightGuardedMasterSemantics` prouve que l'UNSAT de la formule
  maître gardée établit cette interface pour les 54 couples ;
- `R45DegreeEightGuardedMaster` identifie exactement la CNF certifiée, compose
  son rejeu cube-et-conquête et exporte
  `no_root_has_redDegree_eight_certified` sans hypothèse résiduelle.

`R45DegreeEightPilotAssembly` spécialise ce cœur générique. Son théorème
terminal `no_degreeEight_l22r01_of_catalogue_witnesses` prouve la contradiction
pour toute branche `(4,5)`-libre de `K25` de degré rouge 8 qui porte exactement
les témoins `gen358` parent 22 et `gen4416` cible 1. Les 148 unités sont donc
transportées et le LRAT est utilisé de bout en bout, sans hypothèse SAT de
relabeling ajoutée à la main.

La contradiction n'est plus limitée à une feuille étiquetée : le maître gardé
et sa couverture fournissent maintenant
`AllAdmissibleDegreeEightPairsContradictory`. Le théorème compilé
`no_root_has_redDegree_eight_certified` ferme donc le cas degré rouge 8 pour
toute racine, sans hypothèse certificative résiduelle.

Le module `R45RemainingDegrees` compose cette fermeture avec la réduction de
parité déjà certifiée aux degrés `{8, 10, 12}`. Le théorème
`certified_exists_red_degree_ten_or_twelve` prouve désormais que tout
contre-exemple hypothétique à `R(4,5) ≤ 25` possède un sommet de degré rouge
10 ou 12. Il reste donc exactement ces deux branches structurelles à fermer,
et non l'ensemble de la fenêtre `7..13`.

Il n'y a aucun `sorry` ou `admit`. `#print axioms` expose les axiomes
classiques/quotients usuels et les ponts natifs explicitement employés pour
le rejeu LRAT et les contrôles finis par `native_decide`. La frontière de
confiance pratique comprend donc le noyau Lean ainsi que le compilateur et le
runtime natifs pour ces ponts ; un rejeu purement noyau demanderait un mode de
certification plus coûteux.

C'est une certification indépendante Lean/LRAT, formellement vérifiable, mais
ni une première formalisation ni une nouveauté mathématique revendiquée. Le
[catalogue de McKay](https://users.cecs.anu.edu.au/~bdm/data/ramsey.html)
listait déjà deux graphes `R(4,4,16)`, et Gauthier–Brown,
[*A Formal Proof of R(4,5)=25*](https://arxiv.org/abs/2404.01761), formalise en
HOL4 l'énumération et la couverture pertinentes. Une publication ne serait
défendable que si l'architecture Lean/LRAT ou la méthode de certification
apporte une distinction suffisante. Ce n'est ni une nouvelle borne de Ramsey,
ni une preuve de `R(4,5) ≤ 25`, ni une avancée directe sur la valeur exacte de
`R(5,5)`.

Pour le pilote degré 8, la chaîne catalogue → permutation globale → unités
DIMACS → maître gardé → couverture LRAT → théorème terminal est complète sur
les 54 couples. Cette fermeture est une certification Lean/LRAT indépendante,
mais ni une preuve de `R(4,5) ≤ 25` ni une revendication de nouveauté
mathématique globale. Les deux degrés racine 10 et 12 nécessaires à cette
borne restent à traiter.

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

### Exhaustivité des catalogues `R(3,5,n)`, `n≤14`

Le certificat par extensions d’un sommet couvre les quinze niveaux jusqu’à
l’ordre 14. Sa partie jusqu’à l’ordre 10, utilisée par la branche `R(5,5)`,
contient :

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
3. Certifier les autres cas de degré racine de `R(4,5,25)`, puis composer leur
   couverture avec le cas degré 8 maintenant fermé pour obtenir
   `R(4,5) ≤ 25` et instancier la borne globale de degrés déjà formalisée.
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
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R55Branch.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R44RootedMixedCNFSemantics.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R44RootedGen4416Cover.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R44Gen4416Classification.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R44Gen4416TargetAudit.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightGen4416Bridge.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightGlobalPermutation.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightRawGen4416Bridge.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightGen358UnitsBridge.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightGen4416UnitsBridge.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightLeafAssemblyCore.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightPilotSemantics.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightReducedAssignment.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightPilotAssembly.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightBranchComposition.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightGuardedMasterSemantics.lean` ;
- `work/vendor/lrat-catcher/LRATCatcher/Tests/R45DegreeEightGuardedMaster.lean`.

La suite locale contient 37 tests Python historiques, tous réussis. Les huit
contrôles de régression propres au classifieur enraciné réussissent également.
Reproduction ciblée depuis la racine du dépôt :

```powershell
python -m unittest scripts.r45_d8_pilot.test_gen4416_rooted_classifier `
  scripts.r45_d8_pilot.test_gen4416_rooted_proof_artifacts
python scripts\r45_d8_pilot\gen4416_rooted_classifier.py verify

cd vendor\lrat-catcher
lake build LRATCatcher.Tests.R44Gen4416TargetAudit `
  LRATCatcher.Tests.R44Gen4416Classification `
  LRATCatcher.Tests.R45DegreeEightGen4416Bridge `
  LRATCatcher.Tests.R45DegreeEightGlobalPermutation `
  LRATCatcher.Tests.R45DegreeEightRawGen4416Bridge `
  LRATCatcher.Tests.R45DegreeEightGen358UnitsBridge `
  LRATCatcher.Tests.R45DegreeEightGen4416UnitsBridge `
  LRATCatcher.Tests.R45DegreeEightLeafAssemblyCore `
  LRATCatcher.Tests.R45DegreeEightReducedAssignment `
  LRATCatcher.Tests.R45DegreeEightPilotAssembly `
  LRATCatcher.Tests.R45DegreeEightBranchComposition `
  LRATCatcher.Tests.R45DegreeEightGuardedMasterSemantics `
  LRATCatcher.Tests.R45DegreeEightGuardedMaster
```

## Sources publiques

- Catalogue Ramsey de Brendan McKay, qui liste déjà les deux graphes
  `R(4,4,16)` : https://users.cecs.anu.edu.au/~bdm/data/ramsey.html
- Gauthier–Brown, *A Formal Proof of R(4,5)=25*, formalisation HOL4 de
  l'énumération/couverture : https://arxiv.org/abs/2404.01761
- Borne supérieure `R(5,5) ≤ 46` :
  https://arxiv.org/abs/2409.15709
- LRAT-Catcher :
  https://github.com/leansolving/lrat-catcher
