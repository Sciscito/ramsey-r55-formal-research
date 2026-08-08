# Ramsey Quest HUD

Petit panneau latéral pixel-art qui raconte l’avancement d’un projet comme une
quête RPG : étape actuelle, acquis, raretés, événements cycliques et verrous
restants.

Ce dossier est volontairement séparé de la recherche : aucune preuve, clause,
catalogue ou commande scientifique ne dépend de lui. Le HUD ne lit aucun
artefact et n’établit aucune propriété mathématique. Il ne fait qu’afficher un
état rédigé par un humain ou par Codex après vérification.

## Lancer localement

Le plus simple est d’ouvrir `index.html` dans un navigateur. Les quatre fichiers
sont autonomes et aucune ressource réseau n’est chargée.

Un petit serveur statique fonctionne aussi :

```powershell
cd extras/ramsey-quest-hud
python -m http.server 8765
```

Puis ouvrir `http://localhost:8765/`.

Le document est déjà aligné à droite et dimensionné comme une barre latérale.
Il peut également être inclus dans une autre page :

```html
<iframe
  src="extras/ramsey-quest-hud/index.html"
  title="Journal de quête du projet"
  width="390"
  height="900">
</iframe>
```

Il s’agit d’une interface en forme de barre latérale, pas d’une extension qui
modifie la barre native de Codex ou de GitHub.

## Réutiliser pour un autre projet

Copier ce dossier puis éditer **uniquement `ramsey-state.js`**. Le moteur
`hud.js`, la feuille `styles.css` et `index.html` sont génériques. Le titre de
la page et le libellé d'accessibilité se règlent également depuis ce fichier,
via `project.documentTitle` et `project.ariaLabel`.

Par défaut, le thème pixel-art et la mise en page sont gelés entre deux
reprises : on actualise les données de quête, pas l'apparence. Ne modifier les
trois fichiers génériques que si l'utilisateur demande explicitement une
évolution du composant lui-même.

Les sections à adapter sont :

- `project` : titre et vérité publique courte ;
- `checkpoint` : état `working`, `idle` ou `blocked`, date et identifiant ;
- `activity` : ce qui est réellement en cours ;
- `truth` : avertissement empêchant une interprétation trompeuse ;
- `stages` : portes `done`, `current` ou `locked`, avec détail et niveau de
  preuve éventuel ;
- `inventory` : acquis remarquables seulement ;
- `events` : messages qui tournent automatiquement ;
- `timing.eventIntervalMs` : rythme des événements, avec un minimum de trois
  secondes imposé par le moteur.

Les raretés reconnues sont `common`, `rare`, `epic`, `legendary` et `mythic`.
Elles indiquent la rareté ou l’importance narrative d’un acquis, jamais sa
validité scientifique. La validité doit rester exprimée séparément par un
niveau de preuve explicite et par le texte du détail.

## Protocole de reprise avec Codex

À chaque reprise de la tâche principale :

1. Relire le handoff scientifique avant ce fichier.
2. Vérifier le commit, le worktree et les validations pertinentes.
3. Mettre `checkpoint.mode` à `working` et décrire l’action réellement engagée
   dans `activity`.
4. Mettre une porte à `done` uniquement après obtention de l’évidence annoncée.
   Une piste, un calcul exploratoire ou une réduction non certifiée garde son
   niveau honnête.
5. Ajouter un acquis exceptionnel dans `inventory` et un message dans `events`
   seulement lorsqu’il est nouveau et vérifié.
6. Avant le handoff, actualiser la date, le checkpoint, l’action suivante et
   les verrous restants.
7. Ne jamais convertir le nombre de portes franchies en pourcentage de preuve.
   Le nombre affiché est seulement une position dans une carte technique.

Prompt court réutilisable :

> Reprends la tâche depuis le handoff, vérifie d’abord l’état réel, puis mets à
> jour `extras/ramsey-quest-hud/ramsey-state.js`. Indique ce qui est acquis, ce
> qui est exceptionnel, l’action en cours, la prochaine porte et les verrous.
> Garde les niveaux de preuve explicites et n’assimile jamais les portes
> techniques à un pourcentage de preuve.

## Vérification légère

Sans installer de dépendance :

```powershell
node --check ramsey-state.js
node --check hud.js
```

Le HUD respecte `prefers-reduced-motion`, arrête son minuteur lorsque l’onglet
est masqué et n’effectue aucun appel réseau.
