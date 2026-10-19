(() => {
  'use strict';
  const $ = selector => document.querySelector(selector);
  const search = $('#interface-search');
  const module = $('#interface-module');
  const kind = $('#interface-kind');
  const dependency = $('#interface-dependency');
  const status = $('#interface-status');
  const states = {
    proved: {label:'Proof complete · baseline', short:'Proofs complete'},
    local: {label:'Local proof complete', short:'Local proofs complete'},
    pending: {label:'Direct obligation', short:'Direct obligations'},
    defined: {label:'Definition / object', short:'Definitions & objects'},
    unknown: {label:'Source unavailable', short:'Source unavailable'},
  };
  function stateOf(row) {
    if (row.obligation || row.source?.sorry === true) return 'pending';
    if (row.source_is_parent || !row.source?.kind || typeof row.source.sorry !== 'boolean') return 'unknown';
    if (['theorem', 'lemma'].includes(row.source.kind)) return row.axioms?.includes('sorryAx') ? 'local' : 'proved';
    return 'defined';
  }
  function selectStatus(value, owner = '') {
    module.value = owner; status.value = value; kind.value = 'declaration';
    search.value = ''; dependency.value = ''; filter();
  }
  function statusButton(value, count, owner = '') {
    const button = node('button', undefined, 'status-filter state-' + value);
    button.type = 'button'; button.dataset.status = value; button.dataset.owner = owner;
    button.append(node('strong', count.toLocaleString()), node('span', states[value].short));
    button.addEventListener('click', () => selectStatus(value, owner));
    return button;
  }
  function overview(modules) {
    const publicRows = records.filter(row => row.kind === 'declaration');
    const counts = rows => Object.fromEntries(Object.keys(states).map(value => [value, rows.filter(row => row.state === value).length]));
    for (const [value, count] of Object.entries(counts(publicRows))) {
      if (count || value !== 'unknown') $('#interface-summary').append(statusButton(value, count));
    }
    for (const item of modules) {
      const rows = publicRows.filter(row => row.owner === item.name);
      const totals = counts(rows);
      const card = node('article', undefined, 'module-card');
      const button = node('button', undefined, 'module-select');
      button.type = 'button'; button.dataset.module = item.name;
      button.append(node('strong', item.name), node('span', `${rows.length} public interfaces`));
      button.addEventListener('click', () => { module.value = item.name; filter(); });
      const bar = node('div', undefined, 'status-bar');
      bar.setAttribute('role', 'img');
      bar.setAttribute('aria-label', Object.entries(totals).map(([value, count]) => `${states[value].short}: ${count}`).join('; '));
      const breakdown = node('div', undefined, 'module-statuses');
      for (const [value, count] of Object.entries(totals)) {
        if (!count) continue;
        const segment = node('span', undefined, 'state-' + value);
        segment.style.flexGrow = count; segment.title = `${states[value].short}: ${count}`; bar.append(segment);
        breakdown.append(statusButton(value, count, item.name));
      }
      const obligations = node('button', `${item.obligations} registered obligations →`, 'obligation-link');
      obligations.type = 'button';
      obligations.addEventListener('click', () => {
        module.value = item.name; kind.value = 'obligation'; status.value = 'pending';
        search.value = ''; dependency.value = ''; filter();
      });
      card.append(button, bar, breakdown, obligations); $('#interface-modules').append(card);
    }
  }
  const pageSize = 40;
  let records = [], filtered = [], current = 0;
  function node(tag, text, className) {
    const element = document.createElement(tag);
    if (text !== undefined) element.textContent = text;
    if (className) element.className = className;
    return element;
  }
  function link(text, href, download = false) {
    const element = node('a', text);
    element.href = href;
    if (download) element.download = '';
    else { element.target = '_blank'; element.rel = 'noopener'; }
    return element;
  }
  function field(list, title, value) {
    list.append(node('dt', title), node('dd', value));
  }
  function render() {
    const container = $('#interface-records');
    container.replaceChildren();
    for (const row of filtered.slice(current * pageSize, (current + 1) * pageSize)) {
      const card = node('article', undefined, 'interface-card');
      const badges = node('div', undefined, 'badges');
      const labels = {declaration:'Public declaration', generated:'Generated export', obligation:'Registered obligation'};
      badges.append(node('span', row.owner), node('span', labels[row.kind]));
      badges.append(node('span', states[row.state].label, 'state-label state-' + row.state));
      if (row.obligation) badges.append(node('span', row.obligation.status, 'pending'));
      if (row.axioms?.includes('sorryAx')) badges.append(node('span', 'Baseline permits dependency gaps', 'pending'));
      const heading = node('h2'); heading.append(node('code', row.name));
      card.append(badges, heading);
      if (row.source?.statement && !row.source_is_parent) card.append(node('pre', row.source.statement, 'statement'));
      const details = node('details'); details.append(node('summary', 'Locked fields and source'));
      const fields = node('dl');
      field(fields, 'Type fingerprint', row.type_fingerprint);
      if (row.kind !== 'obligation') {
        field(fields, 'Universe parameters', row.universes.length ? row.universes.join(', ') : 'None');
        field(fields, 'Allowed axioms', row.axioms.length ? row.axioms.join(', ') : 'None recorded');
      } else {
        field(fields, 'Defining module', row.module);
        field(fields, 'Body fingerprint', row.body_fingerprint);
      }
      details.append(fields);
      if (row.source) {
        if (row.source.context) {
          details.append(node('h3', 'Source context (before elaboration)'), node('pre', row.source.context));
        }
        if (row.source_is_parent) details.append(node('p', 'Compiler-generated export; source link points to its parent declaration.'));
        details.append(link('Read Lean source ↗', row.source.href));
      } else details.append(node('p', 'No individual source statement is available; consult the module and baseline.'));
      details.append(link('Download baseline ↓', row.baseline, true));
      const proposals = new URLSearchParams({module:row.owner, search:row.name});
      const review = link('Find interface proposals →', '../interfaces/index.html?section=proposals&' + proposals);
      review.dataset.interfaceSection = 'proposals'; review.removeAttribute('target'); details.append(review);
      card.append(details); container.append(card);
    }
    const pages = Math.max(1, Math.ceil(filtered.length / pageSize));
    $('#interface-results').textContent = `${filtered.length} matching entries · ${records.length} total · showing ${filtered.length ? current * pageSize + 1 : 0}–${Math.min((current + 1) * pageSize, filtered.length)}`;
    $('#interface-empty').hidden = filtered.length !== 0;
    $('#interface-page-number').textContent = `Page ${current + 1} of ${pages}`;
    $('#interface-prev').disabled = current === 0;
    $('#interface-next').disabled = current + 1 >= pages;
    for (const button of document.querySelectorAll('.module-select')) {
      button.setAttribute('aria-pressed', String(button.dataset.module === module.value));
    }
    for (const button of document.querySelectorAll('.status-filter')) {
      button.setAttribute('aria-pressed', String(kind.value === 'declaration' && button.dataset.status === status.value && button.dataset.owner === module.value));
    }
  }
  function filter() {
    const words = search.value.trim().toLocaleLowerCase().split(/\s+/).filter(Boolean);
    filtered = records.filter(row => (!module.value || row.owner === module.value) &&
      (!kind.value || row.kind === kind.value) &&
      (!status.value || row.state === status.value) &&
      (!dependency.value || (row.axioms !== undefined &&
        row.axioms.includes('sorryAx') === (dependency.value === 'sorry'))) &&
      words.every(word => row.searchText.includes(word)));
    current = 0; render();
  }
  $('#interface-filters').addEventListener('submit', event => event.preventDefault());
  $('#interface-filters').addEventListener('reset', () => setTimeout(filter, 0));
  search.addEventListener('input', filter);
  for (const control of [module, kind, dependency, status]) control.addEventListener('change', filter);
  $('#interface-prev').addEventListener('click', () => { current--; render(); });
  $('#interface-next').addEventListener('click', () => { current++; render(); });
  window.addEventListener('interfaces:filters', event => {
    const values = event.detail;
    status.value = ''; kind.value = 'declaration'; dependency.value = '';
    if ('search' in values) search.value = values.search;
    if ('module' in values) module.value = values.module;
    filter();
  });
  fetch('data.json').then(response => {
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    return response.json();
  }).then(data => {
    records = data.records.map(row => ({...row, state:stateOf(row), searchText:JSON.stringify(row).toLocaleLowerCase()}));
    for (const item of data.modules) {
      const option = node('option', item.name); option.value = item.name; module.append(option);
    }
    overview(data.modules);
    $('#interface-count').textContent = `${data.modules.length} modules · ${records.filter(row => row.kind === 'declaration').length} public declarations · ${records.filter(row => row.kind === 'obligation').length} registered obligations`;
    $('#interface-audit').textContent = JSON.stringify(data.audit_boundaries, null, 2);
    $('#interface-naming').textContent = JSON.stringify(data.naming, null, 2);
    for (const path of data.downloads) $('#interface-downloads').append(link(path, path, true));
    const query = new URLSearchParams(window.interfaceInitialFilters || location.search);
    search.value = query.get('search') || '';
    if ([...module.options].some(option => option.value === query.get('module'))) module.value = query.get('module');
    filter();
  }).catch(error => {
    $('#interface-results').textContent = `Unable to load interface baselines: ${error.message}. Reload this page or consult the baseline guide.`;
    $('#interface-count').textContent = 'Baselines unavailable';
  }).finally(() => window.hgraph?.ready());
})();
