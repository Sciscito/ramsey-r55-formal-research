# Projet R(5,5) — état vérifiable

## Mise a jour de recherche - nuit du 7 au 8 aout 2026

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
Pris isolément, ce batch historique fermait seulement l'ecran solveur : aucun
LRAT individuel n'avait ete demande. La lacune de reconstruction CNF alors
identifiee a ensuite ete fermee par une reimplementation deterministe autonome
des generateurs du projet. Elle verifie exhaustivement les 2^21 affectations
locales, retrouve 923 012 affectations R(4,4) et exactement 25 200 motifs,
reconstruit les 3 367 437 clauses source dans leur ordre, puis reproduit pour
les 13 cas la simplification, le dedoublonnage et l'ajout des 21 unites. Les
comparaisons sont exactes octet par octet. Le rapport suivi, de SHA-256
5D8D129A2431B7F473AF24B4BE21864FA6CCBE05DB4D347665FCE0749EB35024,
explicite sa propre limite : ce certificat fini partage les representants et
hashes geles et ne constitue pas, a lui seul, un LRAT ou un pont Lean. Cette
limite historique est desormais depassee par le coeur LRAT, la source indexee
et la composition semantique decrits plus bas.

Un premier maillon Lean de ce pont est acquis : `R44Cover6MotifBridge`
decode les six graph6, controle leurs matrices et leurs trois paires
complementaires, puis prouve l'equivalence entre la faussete du bloqueur
DIMACS complet de 21 litteraux et une occurrence induite etiquetee.
`R44Cover6CubeBridge` compile aussi et prouve generiquement qu'un bloqueur de
cube partiel est faux exactement lorsque tous ses bits fixes correspondent;
sous une hypothese explicite de surete du cube, il fournit ensuite
l'occurrence induite.

Le certificat Python suivi `COVER6_CUBE_MOTIF_BRIDGE_V1.json` verifie les six
representants, leur unique completion `R(4,4)`, le transport `S7` bijectif vers
25 200 cubes et 25 200 masques motifs distincts, puis les conditionnements par
334 orbites stabilisatrices sans racine et 38 avec racine projetee. Sa portee
est strictement finie et Python : aucun SAT, LRAT, rejeu Lean, egalite DIMACS
parsee ou theoreme cover6-d8 n'en decoule. Le module Lean
`R44Cover6RepresentativeCubes` compile et traite maintenant les six
representants : bonne formation, 16 a 64 completions, unique completion
`R(4,4)` et permutation explicite vers le motif correspondant.
`R44Cover6S7Transport` prouve en plus symboliquement l'invariance `R(4,4)`,
le transport bit-a-bit des masques, l'invariance de `CubeMatchesLocal` et le
fait que tout cube muni d'un temoin d'orbite vers l'un des six representants
force le motif transporte. Le certificat suivi
`COVER6_CONDITIONED_ORBIT_WITNESSES_V1.json` fournit maintenant 32 880
temoins K7 et 1 200 lifts K6 dans un flux de 15 bits par entree. Son test
exhaustif verifie les 34 080 lignes, puis la vue ordonnee des 3 514 clauses K7
et 2 409 clauses K6 retenues par le coeur. Le rapport a pour SHA-256
`0F04DC3992BE3E87493E369305FB608DD44AE1205363CCBCCCAC601C5CDFB34B`.
Le module
`R44Cover6ConditionedWitnesses` decode maintenant ce flux dans Lean, controle
les clauses et les lifts par deux certificats `native_decide` agreges, puis
construit le fournisseur semantique complet. Le parseur est fail-closed pour
les 5 923 egalites utilisees par la preuve; l'identite octet par octet et les
metadonnees du JSON restent controlees separement par les tests Python.

Un pilote `Master8` remplace par ailleurs les treize residuelles par une seule
formule : `F8`, onze unites de racine, huit clauses de prefixe et trois clauses
de bornes. L'audit des `2^10` affectations retrouve exactement les treize
couples historiques. La formule a 3 367 459 clauses, 189 298 375 octets et le
SHA-256
`3E725132C29E1CAA9D5FD5EA0AD67D8A5A80E61A1241768D36A910DD23FD329D`.
CaDiCaL 2.1.2 la declare UNSAT en 4 598 conflits et a produit un LRAT unique de
128 131 809 octets, SHA-256
`B2ECDACD2D99CD6EA2929C0B370C6AAFD74FE78FDE20FFBDFE68B7D0EF860505`,
avec `--checkproof=2`. Le rejeu Lean brut a ete arrete au plafond de 3 Gio sans
diagnostic ni theorem. Une fermeture de dependances RUP a depuis extrait un
coeur de 6 152 clauses initiales et 7 061 additions. Le CNF reduit fait
292 093 octets; son LRAT remappe fait 754 043 octets. Ce LRAT et un second LRAT
regenere par CaDiCaL sur le meme coeur ont tous deux ete rejoues directement
par LRATCatcher en quelques secondes. Le mapping de 6 152 lignes est une
sous-sequence ordonnee exacte du DIMACS Master8 gele. Le manifeste suivi est
`scripts/r45_d12_cover9_universal/master8_core/MANIFEST.json`.

Ce nouveau resultat certifie l'UNSAT du coeur DIMACS et, au niveau fini, du
Master8 gele qui le contient. Le pont est maintenant aussi formel :
`R44Cover6Master8IndexedSource` definit paresseusement les 3 367 459 clauses,
prouve que les 6 152 indices selectionnent exactement le coeur rejoue, puis
etablit `master8Source_unsat`. Surtout, la voie certifiee ne retient que sept
clauses de tri et `-15`, qui lui suffisent : aucune unite de racine, aucune
borne croisee et aucune disjonction des treize cas. La source normalisee
`F8 + core8` a 3 367 445 clauses, SHA-256
`0133D40DC0458E7CD426F22DA08B525B4197467E539E4446AE94A38E84D7341E`,
et Lean prouve `normalizedSource_unsat`.

`R44Cover6SemanticComposition` prouve la satisfaction des 717
clauses de base et des huit clauses finales, certifie la taxonomie ordonnee
`221 + 3 514 + 2 409 + 8` du coeur et compose ces familles avec
`TwoCenterBranch` et l'UNSAT rejouee. `R44Cover6ConditionedWitnesses` instancie
le `CoreBlockerWitnessProvider` et ferme enfin le theorem terminal
`degreeEight_has_cover6_motif` : toute coloration `R(4,4)`-libre sur 12
sommets dont la racine 0 a degre positif 8 contient une occurrence induite de
l'un des six motifs. La compilation directe passe en 468,853 s, avec un pic
observe de 822,3 Mio et aucun `sorryAx`; le module a pour SHA-256
`55B50818D9C231AF1105B526B4389F68EAB52C70EDCF090C4E16BFAD717007B3`.
C'est un resultat local niveau 4;
`d7`, `d6`, la complementation globale et les gluings K25 restent ouverts, et
aucune nouvelle borne sur `R(5,5)` n'en decoule.

### Cover6, degre 7 : centre minimal et pilote exact

`R44Cover6DegreeSevenMinCenter` prouve maintenant dans Lean qu'apres le tri
de la racine 0 de degre positif 7, le voisinage de sept sommets contient un
centre de degre interne 1 ou 2. Le module final, SHA-256
`16448C8ECA7D22DDAAF734C481553A750FE1857D23F8288C180EECB2759DB6AF`,
a ete recompile sur ces octets exacts en 221,131 s, avec un pic de 823 Mio et
aucun `sorryAx`. `R44Cover6DegreeSevenNormalization` construit maintenant la
permutation qui place ce temoin en sommet 1, le tri final `6+4`, la
decomposition du degre `1+p+q`, les neuf cas et la satisfaction des neuf
clauses DIMACS exactes. Son SHA-256 est
`D9A0BABC4DACDE65404E0C719DF076B2EAC5D0362D5698B8BE8E4F3A34207679`;
la compilation directe et un audit independant passent sans `sorryAx`.
`R44Cover6DegreeSevenR34Normalization`, SHA-256
`1CF0DA9E2B47ED6F502AD1A7701F06D04E36C3DEA9BBE995825B8C1C4FA996B2`,
ferme le wrapper, entre dans le catalogue exhaustif `R(3,4;7)`, releve vers
douze sommets l'isomorphisme inverse correct et fixe les 21 variables de la
branche. `R44Cover6Master7R34IndexedSource`, SHA-256
`6B1650D87BE0F4CC931DF21F180C48451097180D6DFBE09866A0C0B8FCB25A60`,
materialise paresseusement F7 et les neuf sources de branche exactes.

Un auditeur Python separe reconstruit F7 puis les neuf clauses correspondant
exactement aux couples `(1,1..4)` et `(2,0..4)`. F7 a 4 312 419 clauses,
246 507 515 octets et le SHA-256
`85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C`;
le Master7 a 4 312 428 clauses, 246 507 588 octets et le SHA-256
`DFA3F7C3C1ADF2F6C8855FA5F08D11D54BFC826205246E68DAD5F4F5D46A5BBE`.
Un second chemin les reproduit octet par octet. Le rapport suivi a pour
SHA-256 `3CBEF9CAC765E5D9D09E4FF1620D6EFBF31FA31F28136D77C61F17419AB381FF`.

Le premier pilote CaDiCaL, sans LRAT, s'arrete `UNKNOWN` au plafond de
100 003 conflits en 263,82 s, avec 927,67 Mio signales par le solveur. Aucun
budget n'est augmente : ce resultat de niveau 1 indique qu'il faut un split ou
une symetrie supplementaire. Le manifeste suivi
`MASTER7_MIN_CENTER_PILOT_V1.json` a pour SHA-256
`12492F5291582AB59D204EF064CE3A794DD83814E388CF28991259DA8363E5B3`.
Ce premier pilote n'avait produit ni UNSAT, ni LRAT, ni theorem terminal.

Un second pilote plus structurel remplace les neuf couples faibles par les
neuf classes exhaustives `R(3,4;7)` modulo `S7`. Le flux incremental exact a
246 508 227 octets et le SHA-256
`CD4C3BB7D0850F75028346B6CD1AA4493D9FD837BFC595503D3E5DA750703180`.
CaDiCaL ferme les neuf cubes sur neuf, sans inconclusif, en 16 893 conflits,
29,16 s reels et 1 083,19 Mio maximum. Le premier cube, le motif exact
``FG`Xo``, ferme sans conflit et sert d'oracle de polarite. Lean ferme aussi
directement cette branche par une occurrence induite dans
`R44Cover6DegreeSevenR34Oracle`, SHA-256
`F8F041AB29F7DC1181380F8D15E696E20EB906112EF653F63366F825CE5E4404`.
Le rapport suivi
`MASTER7_R34_CATALOGUE9_PILOT_V1.json` a pour SHA-256
`205E5F05132D7EDDA4C8ED14A8773CA12EB7BAEC2CB79EEC3391DD855071C323`.
Le premier representant non trivial certifie est ``F`GOW``. Son coeur suivi
contient 5 807 clauses initiales, 9 475 additions RUP et zero etape RAT; le
replay LRAT Lean passe en 2,9858 s avec 209 424 384 octets au pic. Le manifeste
portable a pour SHA-256
`8A7E66C31F1AF2E8BA81F4FE765D6D1D1EAC2C457EB8FCEB80C1DCC1313C1409`
et le rapport suivi
`MASTER7_R34_FGRAVEGOW_LRAT_CORE_V1.json` a pour SHA-256
`2AA548863E6CD3D4BB78910AB289F9EB2F76A0D6DBF2D0F85E3C9E6CBFFD028E`.
`R44Cover6Master7R34FgraveGowCore`, SHA-256
`3266F3DACE0854B665FA2374B0742D5FA0BBD0D4AB79B49BC32DDA21A4320C29`,
verifie en plus que les 5 807 indices selectionnent exactement ce coeur depuis
la source de branche F7+21, rejoue le LRAT et prouve cette source complete
UNSAT. `R44Cover6Master7R34FgraveGowSemantics`, SHA-256
`9608990A7CD482A3526E7A7A788D8ED158F3FF3C34E9AA57087B331A4BB20493`,
ajoute 5 623 temoins compacts pour les 168 clauses de base, 3 227 bloqueurs K7,
2 396 bloqueurs K6 et 16 unites du coeur, puis compose leur semantique avec
l'UNSAT LRAT jusqu'a la contradiction. La feuille ``F`GOW`` est donc fermee
semantiquement. La feuille `FoDPO` est maintenant fermee de la meme facon :
son coeur portable contient 7 686 clauses initiales et 12 107 additions RUP,
son replay Lean suivi passe, et 7 485 temoins certifient exactement les
183 clauses de base, 4 221 bloqueurs K7, 3 264 bloqueurs K6 et 18 unites.
`R44Cover6Master7R34FoDPOCore`, SHA-256
`09F9244CD512AEDE1BFCDF6434E893F9695B6E08B703DC3D87E598B5083540B8`,
et `R44Cover6Master7R34FoDPOSemantics`, SHA-256
`5C41697844EB1CBB0C31A5F8F93F158407979A28973D637027623A419096FDC4`,
composent cette branche jusqu'a False. Le manifeste du coeur a pour SHA-256
`5E215018884DEA2708EE184E084D3F74F3D0D7AC9EFD8D234EB57404B0E516EF`.
La feuille `FCUj_` est aussi fermee : coeur de 1 104 clauses rejoue par Lean,
990 temoins, puis typecheck semantique en 82,26 s. Cinq representants non
triviaux et la composition du catalogue avec `S7` restent ouverts. Il n'existe
encore ni theorem Lean
`cover6-d7`, ni nouvelle borne de Ramsey.

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
obtenue. La fermeture solveur 13/13 et le replay CNF exact de cover6-d8
ont depuis ete completes par le coeur LRAT et le theorem Lean local de niveau
4 decrit en tete de fichier. Ce resultat est publiable comme certificat local
apres audit documentaire, mais ne ferme ni d7/d6 ni un gluing global. La
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
et l'ancien vérificateur ne reconstruisait ni chaque clause globale ni les
réductions vers les résiduelles. Cette lacune est désormais fermée par le
replay autonome décrit en tête de fichier : source ordonnée et treize
réductions correspondent octet par octet aux artefacts gelés.

Les 13/13 résiduelles à deux centres existent désormais, contiennent chacune
les 21 unités attendues et ont rendu UNSAT sans preuve. Leur provenance finie
depuis la source est certifiée au niveau du replay Python. Elles n'ont toujours
pas de LRAT individuel; cette route est toutefois supersédée par le Master8
normalisé, son cœur LRAT rejoué et la composition Lean complète décrite en
tête de fichier, qui prouve le théorème local `cover6-d8`.

Le compteur global demeure donc **0/12 cas mathématiques de degré 12
fermés**. Aucune nouvelle borne de Ramsey n’est revendiquée. Le minimum
cover6 et la certification cover9 degré 8 sont des lemmes computationnels
potentiellement publiables, sous réserve d’un audit bibliographique plus large
et de leur injection dans les degrés restants et les gluings globaux. Le relais complet pour la
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
