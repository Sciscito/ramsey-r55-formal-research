'use strict';

// This is the only project-specific file. The HUD engine never reads proof
// artifacts: every claim below must be updated from the verified handoff.
window.RAMSEY_QUEST_STATE = {
  schemaVersion: 1,

  project: {
    kicker: 'R55 // SIDE QUEST',
    title: 'RAMSEY QUEST',
    boundLabel: 'Intervalle public : 43 ≤ R(5,5) ≤ 46'
  },

  checkpoint: {
    label: 'PR #2 · replay CNF + motifs Lean',
    updatedAt: '2026-08-07',
    mode: 'working',
    modeLabel: 'EN COURS'
  },

  activity: {
    eyebrow: 'QUÊTE ACTUELLE',
    title: 'Pont graphes ↔ CNF ↔ Lean',
    detail: 'F8 → F(p,q) est exact et le bloqueur complet des six motifs est formalisé; relier maintenant les cubes partiels à la formule globale puis aux branches Lean.'
  },

  truth: {
    label: 'RÈGLE D’HONNÊTETÉ',
    detail: '4 portes techniques sur 8 sont franchies. Cela ne signifie pas 50 % d’une preuve : une seule porte verrouillée peut encore contenir l’essentiel de la difficulté.'
  },

  stages: [
    {
      id: 'checkpoint',
      label: 'Checkpoint propre et poussé',
      state: 'done',
      rarity: 'common',
      proofLevel: null,
      detail: 'La PR #2 porte le HUD séparé, le replay CNF exact et le pont Lean des motifs; les validations ciblées sont vertes.'
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
      state: 'current',
      rarity: 'legendary',
      proofLevel: null,
      detail: 'Source, substitutions, unités et 13 résiduelles sont exactes. Lean relie déjà chaque bloqueur complet à une occurrence induite; restent les cubes conditionnés, la formule globale et TwoCenterBranch.'
    },
    {
      id: 'certified-pilot',
      label: 'Pilote motif certifié',
      state: 'locked',
      rarity: 'legendary',
      proofLevel: null,
      detail: 'Tester une obligation motif-conditionnée sans signature_lex. Continuer seulement si le gain calculatoire est convaincant.'
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
    }
  ],

  events: [
    {
      glyph: '⚒',
      kind: 'work',
      title: 'Le héros inspecte le pont',
      detail: 'Action active : relier cubes partiels, formule globale et branches Lean.'
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
      title: 'PROCHAINE PORTE · pilote certifié',
      detail: 'Après le pont exact, tester une seule obligation et arrêter si le gain reste inférieur à ×2.'
    }
  ],

  timing: {
    eventIntervalMs: 6500
  }
};
