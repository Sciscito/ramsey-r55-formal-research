'use strict';

(() => {
  const root = document.getElementById('quest-hud');
  const state = window.RAMSEY_QUEST_STATE;

  if (!root || !state) {
    throw new Error('Ramsey Quest HUD: #quest-hud or RAMSEY_QUEST_STATE is missing.');
  }

  const requiredArrays = ['stages', 'inventory', 'events'];
  requiredArrays.forEach((key) => {
    if (!Array.isArray(state[key])) {
      throw new TypeError(`Ramsey Quest HUD: ${key} must be an array.`);
    }
  });

  const byId = (id) => document.getElementById(id);
  const setText = (id, value) => {
    const node = byId(id);
    if (node) node.textContent = value ?? '';
  };

  const rarityNames = {
    common: 'COMMUN',
    rare: 'RARE',
    epic: 'ÉPIQUE',
    legendary: 'LÉGENDAIRE',
    mythic: 'MYTHIQUE'
  };

  const doneCount = state.stages.filter((stage) => stage.state === 'done').length;
  const currentIndex = state.stages.findIndex((stage) => stage.state === 'current');
  const technicalPosition = currentIndex >= 0 ? currentIndex : doneCount;
  const fillRatio = state.stages.length > 1
    ? Math.min(1, technicalPosition / (state.stages.length - 1))
    : 0;

  root.style.setProperty('--gate-fill', `${(fillRatio * 100).toFixed(2)}%`);

  setText('quest-kicker', state.project.kicker);
  setText('quest-title', state.project.title);
  setText('bound-label', state.project.boundLabel);
  setText('checkpoint-label', state.checkpoint.label);
  setText('updated-label', `MAJ ${state.checkpoint.updatedAt}`);
  setText('current-eyebrow', state.activity.eyebrow);
  setText('current-title', state.activity.title);
  setText('current-detail', state.activity.detail);
  setText('current-gate', currentIndex >= 0
    ? `PORTE ${currentIndex + 1}/${state.stages.length}`
    : `${doneCount}/${state.stages.length} PORTES`);
  setText('truth-label', state.truth.label);
  setText('truth-detail', state.truth.detail);
  setText('inventory-count', `${state.inventory.length} OBJETS`);

  const mode = byId('quest-mode');
  mode.textContent = state.checkpoint.modeLabel;
  mode.dataset.mode = state.checkpoint.mode;

  const stageList = byId('stage-list');
  const selectStage = (stage) => {
    setText('selected-title', stage.label);
    setText('selected-copy', stage.detail);
    const rarity = byId('selected-rarity');
    rarity.textContent = [rarityNames[stage.rarity] || stage.rarity, stage.proofLevel]
      .filter(Boolean)
      .join(' · ');
    rarity.dataset.rarity = stage.rarity;
  };

  state.stages.forEach((stage) => {
    const item = document.createElement('li');
    const button = document.createElement('button');
    const name = document.createElement('span');
    const rarity = document.createElement('span');

    button.type = 'button';
    button.className = 'stage-button';
    button.dataset.state = stage.state;
    button.dataset.rarity = stage.rarity;
    button.setAttribute('aria-label', `${stage.label}, ${rarityNames[stage.rarity] || stage.rarity}`);
    if (stage.state === 'current') button.setAttribute('aria-current', 'step');

    name.className = 'stage-name';
    name.textContent = stage.label;
    rarity.className = 'rarity-chip';
    rarity.dataset.rarity = stage.rarity;
    rarity.textContent = [rarityNames[stage.rarity], stage.proofLevel].filter(Boolean).join(' · ');

    button.append(name, rarity);
    button.addEventListener('click', () => selectStage(stage));
    item.append(button);
    stageList.append(item);
  });

  const selectedStage = state.stages[currentIndex >= 0 ? currentIndex : Math.max(0, doneCount - 1)];
  if (selectedStage) selectStage(selectedStage);

  const inventoryList = byId('inventory-list');
  state.inventory.forEach((entry) => {
    const item = document.createElement('li');
    const gem = document.createElement('span');
    const label = document.createElement('span');
    const meta = document.createElement('span');

    item.className = 'inventory-item';
    gem.className = 'inventory-item__gem';
    gem.dataset.rarity = entry.rarity;
    gem.textContent = '◆';
    gem.setAttribute('aria-hidden', 'true');
    label.textContent = entry.label;
    meta.className = 'inventory-item__meta';
    meta.textContent = [rarityNames[entry.rarity], entry.proofLevel].filter(Boolean).join(' · ');

    item.append(gem, label, meta);
    inventoryList.append(item);
  });

  const eventConsole = root.querySelector('.event-console');
  const hero = byId('pixel-hero');
  const sparkField = byId('spark-field');
  let eventIndex = Math.min(doneCount, Math.max(0, state.events.length - 1));
  let eventTimer = null;

  const prefersReducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  const launchSparks = () => {
    if (prefersReducedMotion) return;
    sparkField.replaceChildren();
    for (let index = 0; index < 9; index += 1) {
      const spark = document.createElement('span');
      spark.className = 'spark';
      spark.style.left = `${10 + ((index * 23) % 82)}%`;
      spark.style.bottom = `${4 + ((index * 11) % 25)}px`;
      spark.style.animationDelay = `${index * 55}ms`;
      sparkField.append(spark);
    }
  };

  const showEvent = (event) => {
    setText('event-glyph', event.glyph);
    setText('event-title', event.title);
    setText('event-detail', event.detail);

    const action = event.kind === 'drop'
      ? 'celebrate'
      : event.kind === 'warning'
        ? 'warning'
        : 'inspect';
    hero.dataset.action = action;

    eventConsole.classList.remove('is-changing');
    void eventConsole.offsetWidth;
    eventConsole.classList.add('is-changing');
    if (event.kind === 'drop') launchSparks();
  };

  const nextEvent = () => {
    if (state.events.length === 0) return;
    eventIndex = (eventIndex + 1) % state.events.length;
    showEvent(state.events[eventIndex]);
  };

  const startEventLoop = () => {
    if (eventTimer || state.events.length < 2) return;
    const interval = Math.max(3000, Number(state.timing?.eventIntervalMs) || 6500);
    eventTimer = window.setInterval(nextEvent, interval);
  };

  const stopEventLoop = () => {
    if (!eventTimer) return;
    window.clearInterval(eventTimer);
    eventTimer = null;
  };

  document.addEventListener('visibilitychange', () => {
    if (document.hidden) {
      stopEventLoop();
    } else {
      nextEvent();
      startEventLoop();
    }
  });

  if (state.events.length > 0) showEvent(state.events[eventIndex]);
  startEventLoop();
})();
