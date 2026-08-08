# Handoff — recherche R(5,5) / R(4,5,25)

## Mise a jour prioritaire - nuit du 7 au 8 aout 2026

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
   bloqueur DIMACS complet de 21 litteraux et l'occurrence induite.
   `R44Cover6CubeBridge` compile et ferme generiquement la semantique du
   bloqueur partiel : faussete si et seulement si les bits fixes du cube
   correspondent, puis occurrence sous une hypothese explicite de surete.
   Cette hypothese est desormais etablie pour les cubes concrets effectivement
   retenus par le coeur, via les temoins conditionnes decrits ci-dessous.
   Le certificat Python `COVER6_CUBE_MOTIF_BRIDGE_V1.json` controle les six
   representants, leur unique completion R(4,4), le transport S7 bijectif vers
   25 200 cubes et motifs distincts, ainsi que 334 orbites stabilisatrices sans
   racine et 38 orbites projetees avec racine. Il importe le replay exact et sa
   portee exclut SAT, LRAT, egalite DIMACS parsee, rejeu Lean et theoreme d8.
   `R44Cover6RepresentativeCubes` compile et certifie maintenant les six
   representants : bonne formation, completions finies, cible R(4,4) unique et
   permutation explicite vers le motif. `R44Cover6S7Transport` prouve
   symboliquement l'invariance R(4,4), le transport des masques et de
   `CubeMatchesLocal`, puis propage les six preuves a tout cube muni d'un
   temoin d'orbite. `COVER6_CONDITIONED_ORBIT_WITNESSES_V1.json` fournit
   maintenant 32 880 temoins K7 et 1 200 lifts K6 en 15 bits par entree. Le
   test exhaustif verifie les 34 080 lignes et la vue exacte des 3 514 + 2 409
   bloqueurs retenus par le coeur. Rapport SHA-256
   0F04DC3992BE3E87493E369305FB608DD44AE1205363CCBCCCAC601C5CDFB34B.
   `R44Cover6ConditionedWitnesses` decode ces
   donnees dans Lean, controle les egalites et lifts par deux certificats
   natifs agreges et construit le fournisseur semantique complet.
   Un pilote `Master8` reunit exactement les 13 branches dans une formule de
   3 367 459 clauses. CaDiCaL la ferme en 4 598 conflits et a produit un LRAT
   unique de 128 131 809 octets (SHA-256
   B2ECDACD2D99CD6EA2929C0B370C6AAFD74FE78FDE20FFBDFE68B7D0EF860505).
   Le rejeu Lean brut a ete arrete a 3 Gio sans theorem. La fermeture RUP a
   ensuite extrait 6 152 clauses initiales et 7 061 additions. Le LRAT remappe
   et un LRAT regenere independamment par CaDiCaL sur ce meme coeur sont tous
   deux acceptes par LRATCatcher. Le mapping est une sous-sequence ordonnee
   exacte du DIMACS Master8 gele; voir
   `scripts/r45_d12_cover9_universal/master8_core/MANIFEST.json`.
   `R44Cover6Master8CoreBridge` prouve la monotonie UNSAT pour une source CNF
   indexee paresseuse. `R44Cover6Master8IndexedSource` instancie maintenant
   cette source, verifie clause par clause la selection des 6 152 indices et
   etablit en Lean `master8Source_unsat`.
   La taxonomie du coeur montre en outre que seules sept clauses de tri et
   `-15` sont retenues. Cette voie certifiee n'emploie donc ni unite racine,
   ni borne croisee, ni disjonction des treize cas. La variante normalisee
   `F8 + core8` a 3 367 445 clauses, SHA-256
   0133D40DC0458E7CD426F22DA08B525B4197467E539E4446AE94A38E84D7341E,
   et Lean prouve `normalizedSource_unsat`.
   Total : 19 657 663 clauses,
   1 077 652 051 octets, 9 889 conflits. Manifeste formule SHA-256
   DDAF42888C6A77C432EC9AA4799D6A24EEDB2088AA25C97C251A82D3986DFB8C;
   batch SHA-256
   AA5E11028D9B8A228E2F6EB7E5F11D0C740BBFDEED9315134C3F1DED8BB1E492.
   Les 13 LRAT residuels ne sont toujours pas produits, mais ils ne sont plus
   requis par la voie normalisee. `R44Cover6SemanticComposition` ferme deja
   les 717 clauses de base et les huit extras, certifie la partition ordonnee
   221/3514/2409/8 du coeur et derive la contradiction contre
   `normalizedCoreSelection_unsat` sous une interface explicite de temoins.
   Cette interface est maintenant instanciee et le theorem Lean
   `degreeEight_has_cover6_motif` est compile : toute coloration R(4,4)-libre
   sur 12 sommets avec racine 0 de degre positif 8 contient l'un des six motifs
   induits. Module SHA-256
   55B50818D9C231AF1105B526B4389F68EAB52C70EDCF090C4E16BFAD717007B3.
   C'est le theorem local `cover6-d8` niveau 4, pas un resultat d6/d7,
   un gluing K25 ou une nouvelle borne sur R(5,5).
2. Cover6 d7 progresse sans etre ferme. Le module Lean
   `R44Cover6DegreeSevenMinCenter` prouve, pour une racine 0 de degre positif
   7, l'existence dans son voisinage d'un centre de degre interne 1 ou 2.
   SHA-256 final recompile :
   16448C8ECA7D22DDAAF734C481553A750FE1857D23F8288C180EECB2759DB6AF.
   `R44Cover6DegreeSevenNormalization`, SHA-256
   D9A0BABC4DACDE65404E0C719DF076B2EAC5D0362D5698B8BE8E4F3A34207679,
   ferme ensuite la permutation du temoin, le tri `6+4`, les neuf cas et les
   neuf clauses DIMACS exactes. Le wrapper est maintenant ferme dans
   `R44Cover6DegreeSevenR34Normalization` : il entre dans le catalogue
   exhaustif R(3,4;7), releve l'isomorphisme inverse correct vers Fin 12 et
   fixe les 21 variables de branche. `R44Cover6Master7R34IndexedSource`
   fournit ensuite F7 et les neuf sources de branche exactes, paresseusement.
   L'audit fini separe reconstruit F7 (4 312 419 clauses, SHA
   85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C)
   et le Master7 exact a neuf couples (4 312 428 clauses, SHA
   DFA3F7C3C1ADF2F6C8855FA5F08D11D54BFC826205246E68DAD5F4F5D46A5BBE).
   Le premier pilote CaDiCaL sans LRAT reste UNKNOWN a 100 003 conflits en
   263,82 s; il ne justifie pas une hausse de budget. Rapport pilote SHA-256
   12492F5291582AB59D204EF064CE3A794DD83814E388CF28991259DA8363E5B3.
   Le split structurel suivant fixe les neuf classes exhaustives R(3,4;7)
   modulo S7 : 9/9 cubes UNSAT, 0 inconclusif, 16 893 conflits et 29,16 s.
   Rapport SHA-256
   205E5F05132D7EDDA4C8ED14A8773CA12EB7BAEC2CB79EEC3391DD855071C323.
   La branche oracle ``FG`Xo`` est maintenant fermee directement dans Lean
   comme occurrence induite, sans SAT; module SHA-256
   F8F041AB29F7DC1181380F8D15E696E20EB906112EF653F63366F825CE5E4404.
   Le premier representant non trivial, ``F`GOW``, possede maintenant un coeur
   suivi de 5 807 clauses initiales et 9 475 additions RUP, rejoue par Lean en
   2,9858 s avec environ 200 Mio. Manifeste SHA-256
   8A7E66C31F1AF2E8BA81F4FE765D6D1D1EAC2C457EB8FCEB80C1DCC1313C1409.
   `R44Cover6Master7R34FgraveGowCore`, SHA-256
   3266F3DACE0854B665FA2374B0742D5FA0BBD0D4AB79B49BC32DDA21A4320C29,
   relie formellement les 5 807 indices a la source F7+21 et prouve cette source
   de branche UNSAT. `R44Cover6Master7R34FgraveGowSemantics`, SHA-256
   9608990A7CD482A3526E7A7A788D8ED158F3FF3C34E9AA57087B331A4BB20493,
   certifie 5 623 temoins pour les 5 807 clauses selectionnees et compose la
   coloration relabellisee jusqu'a False. `FoDPO` est maintenant la seconde
   feuille non triviale fermee : coeur portable de 7 686 clauses et 12 107
   additions RUP, replay Lean suivi, puis 7 485 temoins pour les
   183+4 221+3 264+18 clauses selectionnees. Les modules
   `R44Cover6Master7R34FoDPOCore` et
   `R44Cover6Master7R34FoDPOSemantics` ont respectivement les SHA-256
   09F9244CD512AEDE1BFCDF6434E893F9695B6E08B703DC3D87E598B5083540B8 et
   5C41697844EB1CBB0C31A5F8F93F158407979A28973D637027623A419096FDC4.
   Le second typecheck passe en 593,867 s sous le cap de 600 s. `FCUj_` est
   maintenant la troisieme feuille non triviale fermee : coeur de 1 104 clauses
   rejoue par Lean, 990 temoins, puis composition semantique jusqu'a False en
   82,26 s. Cinq feuilles non triviales et la composition catalogue/S7 restent
   ouvertes.
3. Strate minimum-anchor d20,c10 vide. Le record officiel unique
   R(4,5,20,e=100) a les degres 9^2 10^16 11^2, donc aucun voisinage de
   minimum 10. SHA du record :
   D1D1FF46BD5D153B51D7DA094F6BF459BCEAEFDA65EB4941EAD0BB9B09C897CD.
   Totaux corriges : K43 1509 -> 1196; squelette K45 1815 -> 1502.
4. Ecran K43 negatif mais informatif. Sur huit feuilles representatives,
   une est UNSAT sans LRAT (95 conflits) et sept sont UNKNOWN a 100 000
   conflits. Toutes les CNF temporaires ont ete supprimees. Journal SHA-256
   4B8F4F8ED8A7A937AA0127FB7732F375202E68CDF818EAA6F3EF1D511074A5C6.
5. K45. L'identite d'exces n'elimine aucun degre avec les seules bornes e/E,
   malgre une contrainte de voisinage quasi extremal. La generation brute a
   ete abandonnee et le fichier partiel de 114 449 417 octets nettoye.
6. Chaine jouet semantique fermee. Sur K5, l'encodage declaratif de l'absence
   de triangle monochromatique et de P3 positif induit donne exactement 80
   clauses; le LRAT CaDiCaL est rejoue dans Lean jusqu'au theoreme terminal.
   Les tests mutants rejettent notamment, avant replay, une formule rendue
   trivialement UNSAT par une clause vide; un certificat valide eventuel ne
   pourrait donc pas masquer cette mauvaise formule. Le rejeu Lean est force
   hors cache avec `lake env lean`. Ceci valide le noyau declaratif au niveau
   4 pour le jouet seulement, pas les etapes deux-centres de cover6.
7. Quotient K45 catalogue-relatif. Le bloc exclusif d'une arete est R(4,4).
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
S:\CodexResearchCache\ramsey-formal\lrat-work\r45-cover6-master7-mincenter-v1
et
S:\CodexResearchCache\ramsey-r55-k43-screen\pilot-v1.
Les catalogues et rapports du nouveau pilote restent sous
S:\CodexResearchCache\ramsey-formal\catalogues.
L'archive officielle r45extreme.tar.gz reste sur S: (90 599 728 octets,
SHA-256
9CFAC9DBD1C209CFA342E5D5424DF2A7A3FBB008CA00BF0A992E5BBE72F925B6).

Prochaine sequence recommandee :

1. conserver verts le replay exact d8, le coeur LRAT compact, la source Lean
   indexee et le theorem terminal `degreeEight_has_cover6_motif`;
2. conserver verts MinCenter, la normalisation `6+4`, le wrapper catalogue R34
   et la source F7 indexee;
3. produire et rejouer les cinq certificats non triviaux encore ouverts
   (`FG`Xo` est un motif direct; `F`GOW`, `FoDPO` et `FCUj_` sont fermes), puis
   composer completude du catalogue et invariance S7;
4. formaliser le transport global par complement;
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
scripts/r45_d12_cover9_universal/COVER6_CUBE_MOTIF_BRIDGE_V1.json,
`COVER6_CONDITIONED_ORBIT_WITNESSES_V1.json`,
`COVER6_D7_MIN_CENTER_SOURCE_AUDIT_V1.json`,
`MASTER7_MIN_CENTER_PILOT_V1.json`,
`MASTER7_R34_CATALOGUE9_PILOT_V1.json`,
`MASTER7_R34_FGRAVEGOW_LRAT_CORE_V1.json`,
`scripts/r45_d12_cover9_universal/master7_r34_fgravegow_core/MANIFEST.json`,
`MASTER7_R34_FODPO_LRAT_CORE_V1.json`,
`scripts/r45_d12_cover9_universal/master7_r34_fodpo_core/MANIFEST.json`,
`MASTER7_R34_FCUJ_LRAT_CORE_V1.json`,
`scripts/r45_d12_cover9_universal/master7_r34_fcuj_core/MANIFEST.json`,
`MASTER8_CORE_TAXONOMY_V1.json`,
`scripts/r45_d12_cover9_universal/master8_core/MANIFEST.json` et les modules
Lean `R44Cover6CubeBridge`, `R44Cover6RepresentativeCubes`,
`R44Cover6S7Transport`, `R44Cover6Master8IndexedSource`,
`R44Cover6SemanticComposition`, `R44Cover6ConditionedWitnesses`,
`R44Cover6DegreeSevenMinCenter`,
`R44Cover6DegreeSevenNormalization`,
`R44Cover6DegreeSevenR34Normalization`,
`R44Cover6Master7R34IndexedSource`,
`R44Cover6DegreeSevenR34Oracle`,
`R44Cover6Master7R34FgraveGowCore`,
`R44Cover6Master7R34FgraveGowSemantics`,
`R44Cover6Master7R34FoDPOCore`,
`R44Cover6Master7R34FoDPOSemantics`,
`R44Cover6Master7R34FCUjCore`,
`R44Cover6Master7R34FCUjSemantics`, puis
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
- compilations Lean directes supplementaires : PASS pour
  `R44Cover6CubeBridge`, `R44Cover6RepresentativeCubes` et
  `R44Cover6S7Transport`; le dernier transporte les six preuves a toute orbite
  munie d'un temoin explicite;
- coeur Master8 : mapping exact 6 152 clauses, LRAT remappe de 754 043 octets
  et LRAT CaDiCaL regenere de 777 661 octets; les deux replays Lean directs
  passent. `R44Cover6Master8CoreBridge` fournit le transfert generique et
  `R44Cover6Master8IndexedSource` compile directement avec les theoremes
  `master8Source_unsat` et `normalizedSource_unsat`;
- taxonomie du coeur : 221 clauses base, 3 514 bloqueurs K7, 2 409 bloqueurs
  K6 et 8 finales; replay integral opt-in et empreinte core8 exacts;
- composition terminale : les 34 080 temoins conditionnes passent le controle
  exhaustif; `R44Cover6SemanticComposition` compile directement en 4,6 s et
  `R44Cover6ConditionedWitnesses` compile directement en 468,853 s puis via le
  build cible en 472,229 s, sans `sorryAx` et avec un pic d'environ 822 Mio;
- d7 : audit source complet et deux empreintes exactes PASS; MinCenter,
  normalisation, wrapper catalogue R34 et source indexee compilent sans
  `sorryAx`; le split structurel ferme 9/9 au solveur. La feuille non triviale
  ``F`GOW`` a maintenant un coeur 5 807 + 9 475 all-RUP suivi et un replay Lean
  PASS en 2,9858 s, pic 209 424 384 octets; le pont source/coeur et la
  semantique des 5 807 clauses selectionnees compilent jusqu'a la contradiction
  en 497,34 s, sans `sorryAx`. `FoDPO` ferme de meme 7 686 clauses selectionnees
  et 7 485 temoins en 593,867 s; `FCUj_` ferme 1 104 clauses et 990 temoins en
  82,257 s. Les trois replays et compositions n'utilisent aucun `sorryAx`;
- rejeu catalogue final : 103 706 + 546 356 records R(4,4), zero trou,
  70,65 s; rapport SHA-256
  B85E57FA3D7D25A901DD98E387264B8B47FB6CC71F8721FA7CD07BD7DC1E3203;
- manifeste structural SHA-256
  C17EA950F1E02AAF1223AA9E230208498D2ADC7AAA7077A488435D371FE8B614;
- parse PowerShell, AST Python, JSON et whitespace : PASS.

Le `verify-source.ps1` historique complet n'a pas ete relance : il rehache et
rejoue notamment 2,4 Gio de preuves sans rapport avec les fichiers modifies.
Les chemins touches ont ete testes directement, et le script integre desormais
  les modules Lean locaux ainsi que les replays de coeur d8, ``F`GOW``, `FoDPO`
  et `FCUj_` avec
compilation forcee hors cache, car Lake ne suit pas les octets CNF/LRAT comme
dependances.

Checkpoint scientifique de la nuit du 7 au 8 août 2026. Ce fichier est la source de reprise
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
- d7 : 4 312 419 clauses, 17 cas dans le découpage générique historique;
  l'argument centre-minimal audité réduit la future normalisation à 9 cas,
  mais son générateur et sa preuve Lean ne sont pas encore construits
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

Cette note est désormais supersédée pour la voie normalisée : les treize
LRAT résiduels n'existent toujours pas, mais le cœur Master8 possède deux
rejeux LRAT Lean et la composition sémantique ferme `cover6-d8`. Aucun
résultat universel tous degrés ni nouvelle borne n'est revendiqué.

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

1. conserver verts le replay exact d8, le cœur Master8, sa source Lean et le
   théorème terminal `degreeEight_has_cover6_motif` ;
2. conserver verts MinCenter, la normalisation d7, le wrapper catalogue R34,
   la source F7 indexée et les feuilles closes ``F`GOW`` / `FoDPO` / `FCUj_` ;
3. certifier les cinq feuilles R34 non triviales encore ouvertes, puis composer
   catalogue, symétrie `S7` et sémantique en un
   théorème local d7 ;
4. formaliser le transport global par complément `d ↔ 11-d` ;
5. composer replays et branches Lean, puis réinjecter le lemme dans les 12
   gluings globaux ;
6. audit bibliographique élargi et paquet portable avant publication.

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
- Master7 centre minimal :
  `S:\CodexResearchCache\ramsey-formal\lrat-work\r45-cover6-master7-mincenter-v1`
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
$out7 = 'S:\CodexResearchCache\ramsey-formal\lrat-work\r45-cover6-master7-mincenter-v1'
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
& $py -B -m scripts.r45_d12_cover9_universal.audit_cover6_d7_min_center_source quick
& $py -B -m scripts.r45_d12_cover9_universal.materialize_cover6_d7_min_center_master verify --directory $out7
```

Les 13 cas sont déjà produits et leur replay exact est acquis. La voie Master8
normalisée possède désormais son coeur LRAT, sa source indexée et son théorème
sémantique Lean; il n'est donc pas utile de produire treize LRAT individuels
pour fermer d8. Avant toute régénération historique, rehacher le rapport suivi
et rejouer `exact_replay_cover6_d8 all`. Le runner refuse d’écraser un batch :
choisir un nouveau `--batch-name`. La priorité nouvelle est d7 à neuf cas.

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
