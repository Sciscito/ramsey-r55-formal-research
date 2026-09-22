'use strict';

// This is the only project-specific file. The HUD engine never reads proof
// artifacts: every claim below must be updated from the verified handoff.
window.QUEST_HUD_STATE = {
  schemaVersion: 1,

  project: {
    kicker: 'R55 // SIDE QUEST',
    title: 'RAMSEY QUEST',
    documentTitle: 'Ramsey Quest HUD',
    ariaLabel: 'Suivi ludique de la recherche Ramsey',
    boundLabel: 'Intervalle public : 43 ≤ R(5,5) ≤ 46'
  },

  checkpoint: {
    label: 'BRANCHE · d7 trois feuilles closes',
    updatedAt: '2026-08-08',
    mode: 'working',
    modeLabel: 'EN COURS'
  },

  activity: {
    eyebrow: 'QUÊTE ACTUELLE',
    title: 'Certifier les cinq feuilles d7 restantes',
    detail: 'F`GOW, FoDPO et FCUj_ sont closes jusqu’à False. Action suivante : industrialiser les cinq représentants non triviaux restants, puis composer le catalogue modulo S7.'
  },

  truth: {
    label: 'RÈGLE D’HONNÊTETÉ',
    detail: '5 portes techniques sur 8 sont franchies; la porte 6 est en cours. F`GOW, FoDPO et FCUj_ sont closes sémantiquement; cinq représentants et la composition modulo S7 restent. Il n’y a ni nouvelle borne Ramsey ni théorème cover6-d7 global.'
  },

  stages: [
    {
      id: 'checkpoint',
      label: 'Dernier checkpoint GitHub',
      state: 'done',
      rarity: 'common',
      proofLevel: null,
      detail: 'Le checkpoint GitHub réunit le HUD réutilisable, le théorème local d8, les ponts Master8/S7 et les trois feuilles d7 closes.'
    },
    {
      id: 'toy-chain',
      label: 'Jouet CNF → LRAT → Lean',
      state: 'done',
      rarity: 'epic',
      proofLevel: 'L4',
      detail: 'Une chaîne miniature complète a été fermée sur K5, avec mutants négatifs et rejeu Lean forcé. Elle certifie seulement le jouet.'
    },
    {
      id: 'exclusive-block',
      label: 'Bloc exclusif R(4,4)',
      state: 'done',
      rarity: 'epic',
      proofLevel: 'L4',
      detail: 'Le lemme local du bloc exclusif est formalisé dans le prédicat Ramsey standard. Il ne ferme pas le quotient K45.'
    },
    {
      id: 'small-covers',
      label: 'Covers q=10/11 rejoués',
      state: 'done',
      rarity: 'rare',
      proofLevel: 'L1',
      detail: 'Les catalogues ont été rejoués sans trou et donnent 112 obligations candidates au lieu de 1 502 types. Le résultat reste expérimental.'
    },
    {
      id: 'semantic-bridge',
      label: 'Pont sémantique exact',
      state: 'done',
      rarity: 'legendary',
      proofLevel: 'L4',
      detail: 'Les bloqueurs, S7, la source indexée, le cœur LRAT et les 5 923 témoins sont composés. Lean prouve qu’une racine de degré positif 8 force l’un des six motifs.'
    },
    {
      id: 'certified-pilot',
      label: 'Certifier cover6-d7',
      state: 'current',
      rarity: 'legendary',
      proofLevel: 'L4 feuille',
      detail: 'La branche oracle FG`Xo est fermée directement; F`GOW, FoDPO et FCUj_ sont fermées sémantiquement jusqu’à False. Restent cinq représentants non triviaux et la composition modulo S7.'
    },
    {
      id: 'close-obligations',
      label: '112 obligations fermées',
      state: 'locked',
      rarity: 'legendary',
      proofLevel: null,
      detail: 'Chaque disjonction K45 devra être certifiée, auditée et composée. Le nombre 112 décrit un plan de quotient, pas 112 preuves déjà acquises.'
    },
    {
      id: 'r55-45',
      label: 'BOSS : R(5,5) ≤ 45',
      state: 'locked',
      rarity: 'mythic',
      proofLevel: null,
      detail: 'La percée ne sera revendiquée qu’après une réfutation globale vérifiée de tout coloriage de K45 évitant les K5 monochromatiques.'
    }
  ],

  inventory: [
    {
      label: 'Chaîne jouet formellement close',
      rarity: 'epic',
      proofLevel: 'L4'
    },
    {
      label: 'Lemme du bloc exclusif',
      rarity: 'epic',
      proofLevel: 'L4'
    },
    {
      label: '650 062 graphes rejoués',
      rarity: 'rare',
      proofLevel: 'L1'
    },
    {
      label: 'F8 + 13 résiduelles exactes',
      rarity: 'rare',
      proofLevel: 'L3'
    },
    {
      label: 'Six motifs + bloqueur Lean',
      rarity: 'epic',
      proofLevel: 'L4 local'
    },
    {
      label: '25 200 cubes à complétion unique',
      rarity: 'epic',
      proofLevel: 'L3 fini'
    },
    {
      label: '1 860 cubes racine → 38 orbites',
      rarity: 'legendary',
      proofLevel: 'L3 fini'
    },
    {
      label: 'Master8 UNSAT · cœur double-rejoué',
      rarity: 'legendary',
      proofLevel: 'L2'
    },
    {
      label: 'Cœur 6 152 · double replay Lean',
      rarity: 'legendary',
      proofLevel: 'L4 local'
    },
    {
      label: 'Source core8 UNSAT en Lean',
      rarity: 'legendary',
      proofLevel: 'L4 formule'
    },
    {
      label: 'Transport S7 symbolique',
      rarity: 'epic',
      proofLevel: 'L4 local'
    },
    {
      label: '717 clauses base sémantiques',
      rarity: 'epic',
      proofLevel: 'L4 local'
    },
    {
      label: '34 080 témoins conditionnés exacts',
      rarity: 'legendary',
      proofLevel: 'L3 fini'
    },
    {
      label: '8 extras sémantiques',
      rarity: 'epic',
      proofLevel: 'L4 local'
    },
    {
      label: 'Théorème local d8 · racine 0',
      rarity: 'legendary',
      proofLevel: 'L4'
    },
    {
      label: 'Centre d7 interne 1 ou 2',
      rarity: 'epic',
      proofLevel: 'L4 local'
    },
    {
      label: 'Master7 exact · neuf couples',
      rarity: 'rare',
      proofLevel: 'L3 fini'
    },
    {
      label: 'Écran d7 9/9 · solveur',
      rarity: 'legendary',
      proofLevel: 'L2 local'
    },
    {
      label: 'Oracle d7 FG`Xo · motif direct',
      rarity: 'epic',
      proofLevel: 'L4 branche'
    },
    {
      label: 'Feuille d7 F`GOW · sémantique close',
      rarity: 'legendary',
      proofLevel: 'L4 feuille'
    },
    {
      label: 'Feuille d7 FoDPO · sémantique close',
      rarity: 'legendary',
      proofLevel: 'L4 feuille'
    },
    {
      label: 'Feuille d7 FCUj_ · sémantique close',
      rarity: 'legendary',
      proofLevel: 'L4 feuille'
    }
  ],

  events: [
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP LÉGENDAIRE · FCUj_ complète',
      detail: 'Lean compose les 990 témoins des 1 104 clauses FCUj_ avec son cœur LRAT jusqu’à False en 82,26 s. Trois feuilles non triviales sont désormais closes; cinq restent.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP LÉGENDAIRE · FoDPO complète',
      detail: 'Lean compose 7 485 témoins, 7 686 clauses exactes et le cœur LRAT FoDPO jusqu’à False en 593,87 s sous plafond. FCUj_ a fermé ensuite; cinq représentants restent.'
    },
    {
      glyph: '◆',
      kind: 'drop',
      title: 'JALON HISTORIQUE · cœur FCUj_',
      detail: 'Étape intermédiaire désormais dépassée : après 660 conflits, le cœur FCUj_ tombe à 1 104 clauses initiales et 1 257 dérivées, puis LRATCatcher le ferme en 2,48 s.'
    },
    {
      glyph: '◆',
      kind: 'drop',
      title: 'JALON HISTORIQUE · cœur FoDPO',
      detail: 'Étape intermédiaire désormais dépassée : le cœur exact FoDPO contient 7 686 clauses initiales et 12 107 dérivées, rejouées par LRATCatcher avant la fermeture sémantique.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP LÉGENDAIRE · première feuille d7 complète',
      detail: 'Pour F`GOW, Lean compose la coloration, les 5 623 témoins utiles, les 5 807 clauses du cœur exact et le replay LRAT jusqu’à False. FoDPO et FCUj_ ont fermé depuis; cinq feuilles restent.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'JALON HISTORIQUE · source F7 raccordée',
      detail: 'Étape intermédiaire désormais dépassée : les 5 807 indices F`GOW sélectionnent exactement le cœur suivi; sa sémantique est maintenant composée jusqu’à False.'
    },
    {
      glyph: '◆',
      kind: 'drop',
      title: 'DROP ÉPIQUE · oracle d7 sans SAT',
      detail: 'La branche FG`Xo est déjà l’un des six motifs induits : Lean la ferme directement dans le coloriage relabellisé puis transporte l’occurrence à l’original.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP LÉGENDAIRE · première feuille d7',
      detail: 'La branche R34 F`GOW possède désormais un cœur compact suivi et un replay Lean PASS en environ 2,99 s pour environ 200 MiB. C’est une feuille certifiée, pas un théorème cover6-d7 global.'
    },
    {
      glyph: '⚒',
      kind: 'work',
      title: 'Le héros forge les cinq feuilles restantes',
      detail: 'Action suivante : certifier les cinq représentants non triviaux restants et composer leur couverture modulo S7.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP LÉGENDAIRE · d7 ferme 9/9',
      detail: 'Les neuf classes exhaustives R(3,4;7) modulo S7 sont UNSAT en 16 893 conflits et 29,2 s. Trois feuilles non triviales et l’oracle direct sont certifiés; l’écran complet reste expérimental et ne donne aucune nouvelle borne.'
    },
    {
      glyph: '◆',
      kind: 'drop',
      title: 'DROP ÉPIQUE · neuf portes en Lean',
      detail: 'Permutation du centre, tri 6+4, p∈{1,2}, p+q≥2 et les neuf clauses DIMACS exactes compilent et passent un audit indépendant.'
    },
    {
      glyph: '◆',
      kind: 'drop',
      title: 'DROP ÉPIQUE · centre d7 scellé',
      detail: 'Checkpoint historique : Lean a d’abord prouvé qu’après tri de la racine de degré 7, un voisin possède un degré interne égal à 1 ou 2. La permutation et le tri 6+4 ont depuis été composés.'
    },
    {
      glyph: '!',
      kind: 'warning',
      title: 'ÉCRAN d7 · 100 003 conflits',
      detail: 'Checkpoint historique : le Master7 exact à neuf couples était resté UNKNOWN après 263,8 s. Le split structurel R34 a depuis fermé 9/9 au solveur et lancé la certification feuille par feuille.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'PERCÉE LOCALE · cover6-d8 fermé',
      detail: 'Compilation Lean directe verte : toute coloration R(4,4;12) dont la racine a degré positif 8 contient l’un des six motifs induits. Aucune nouvelle borne globale n’est revendiquée.'
    },
    {
      glyph: '◇',
      kind: 'drop',
      title: 'DROP RARE · d7 réduit à neuf portes',
      detail: 'Checkpoint historique : un centre minimal dans le voisinage de taille 7 a degré interne 1 ou 2. La normalisation d7 à neuf cas et le pont catalogue sont désormais compilés.'
    },
    {
      glyph: '✦',
      kind: 'drop',
      title: 'DOUBLE SCEAU · témoins relus',
      detail: 'Un vérificateur frais a reconstruit indépendamment orbites, rangs de Lehmer, lifts K6 et ordre des 5 923 clauses : aucune faille P0–P2.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP LÉGENDAIRE · flux 34 080/34 080',
      detail: 'Chaque bloqueur conditionné possède un témoin compact vérifié; la vue ordonnée des 5 923 clauses du cœur se réinstancie exactement.'
    },
    {
      glyph: '◆',
      kind: 'drop',
      title: 'DROP ÉPIQUE · huit serrures ouvertes',
      detail: 'Les sept implications de tri et la borne p≤3 sont maintenant satisfaites sémantiquement en Lean par toute branche normalisée.'
    },
    {
      glyph: '◆',
      kind: 'drop',
      title: 'DROP ÉPIQUE · socle 717/717',
      detail: 'Lean relie les clauses Ramsey de base à la branche normalisée, y compris les triangles imposés par la racine de degré huit.'
    },
    {
      glyph: '!',
      kind: 'warning',
      title: 'SAUVEGARDE · GitHub attend sa clé',
      detail: 'Le coffre local est intact et testé. La publication sur la PR #2 reprendra après une reconnexion gh; aucune preuve n’est présentée comme déjà poussée.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP LÉGENDAIRE · 13 salles contournées',
      detail: 'Le cœur n’utilise que sept tris et p≤3 : aucune unité racine, aucune borne croisée, aucune disjonction des 13 cas. Lean prouve l’UNSAT de cette source core8.'
    },
    {
      glyph: '◆',
      kind: 'drop',
      title: 'DROP ÉPIQUE · portail S7',
      detail: 'Un cube muni d’un témoin d’orbite hérite désormais formellement du motif forcé par l’un des six représentants, sans table de 25 200 lignes.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP LÉGENDAIRE · double sceau Lean',
      detail: 'Le LRAT remappé et un second LRAT régénéré par CaDiCaL prouvent l’UNSAT du même cœur; la source Lean indexée relie maintenant ce cœur au Master8 exact.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP LÉGENDAIRE · cœur ×547',
      detail: 'La clause vide ne dépend plus que de 6 152 clauses initiales et 7 061 additions, toutes RUP. Le mapping est une sous-séquence exacte du Master8 gelé.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP LÉGENDAIRE · un seul Master8',
      detail: 'Les 13 branches sont réunies dans une formule exacte : UNSAT en 4 598 conflits. Le cœur, la source indexée et la composition sémantique Lean sont maintenant fermés.'
    },
    {
      glyph: '✦',
      kind: 'drop',
      title: 'DROP ÉPIQUE · six sceaux Lean',
      detail: 'Les six cubes représentants forcent formellement leurs six complétions motifs uniques sous R(4,4).'
    },
    {
      glyph: '✦',
      kind: 'drop',
      title: 'DROP ÉPIQUE · unicité des 25 200 cubes',
      detail: 'Chaque cube possède exactement une complétion R(4,4), et les 25 200 complétions sont exactement les six orbites de motifs.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP LÉGENDAIRE · 38 sceaux de racine',
      detail: 'Les 1 860 cubes projetés se réduisent à 38 représentants sous stabilisateurs, chacun avec un relèvement complet unique.'
    },
    {
      glyph: '◆',
      kind: 'drop',
      title: 'DROP ÉPIQUE · clauses partielles en Lean',
      detail: 'Une clause de cube est fausse exactement lorsque tous ses bits fixés correspondent; le pont générique vers une occurrence induite compile.'
    },
    {
      glyph: '✦',
      kind: 'drop',
      title: 'DROP ÉPIQUE · bloqueur motif Lean',
      detail: 'Les six graph6, leurs paires complémentaires et le bloqueur complet de 21 littéraux ont un pont formel vers les occurrences induites.'
    },
    {
      glyph: '★',
      kind: 'drop',
      title: 'DROP RARE · replay CNF 13/13',
      detail: 'F8 et les 13 réductions F(p,q) correspondent octet par octet aux artefacts gelés.'
    },
    {
      glyph: '◆',
      kind: 'drop',
      title: 'DROP ÉPIQUE · deux briques L4',
      detail: 'La chaîne jouet et le bloc exclusif ont un statut formel local explicite.'
    },
    {
      glyph: '✦',
      kind: 'drop',
      title: 'DROP RARE · rejouage indépendant',
      detail: '650 062 graphes R(4,4) des ordres 10 et 11 ont été vérifiés sans trou de cover.'
    },
    {
      glyph: '!',
      kind: 'warning',
      title: 'GARDE-FOU · aucune borne nouvelle',
      detail: 'Le quotient 1 502 → 112 reste de niveau 1 et aucune obligation K45 globale n’est encore fermée.'
    },
    {
      glyph: '▶',
      kind: 'next',
      title: 'PROCHAINE PORTE · cinq feuilles d7',
      detail: 'Produire et rejouer les cinq certificats non triviaux restants, composer le catalogue R(3,4;7) modulo S7, puis seulement passer à d6.'
    }
  ],

  timing: {
    eventIntervalMs: 6500
  }
};

// Compatibility alias for embeds created before the generic HUD namespace.
window.RAMSEY_QUEST_STATE = window.QUEST_HUD_STATE;
