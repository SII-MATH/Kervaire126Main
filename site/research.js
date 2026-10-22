(() => {
  'use strict';
  const cards = [...document.querySelectorAll('.research-card')];
  const byId = new Map(cards.map(card => [card.id, card]));
  const form = document.querySelector('.research-filters');
  const search = document.querySelector('#research-search');
  const topic = document.querySelector('#research-topic');
  const status = document.querySelector('#research-status');
  const normalize = text => text.normalize('NFKC').toLocaleLowerCase();
  const searchable = new Map(cards.map(card => [card, normalize(card.textContent)]));
  const names = {theta5:'θ₅：平方与乘积', theta6:'θ₆：Moore 谱与阶为二的问题'};

  for (const value of [...new Set(cards.map(card => card.dataset.topic))].sort()) {
    const option = document.createElement('option');
    option.value = value;
    option.textContent = names[value] || value;
    topic.append(option);
  }
  function filter(syncUrl = true) {
    const words = normalize(search.value.trim()).split(/\s+/).filter(Boolean);
    for (const card of cards) {
      card.hidden = Boolean((topic.value && topic.value !== card.dataset.topic) ||
        (status.value && status.value !== card.dataset.status) ||
        words.some(word => !searchable.get(card).includes(word)));
    }
    const count = cards.filter(card => !card.hidden).length;
    document.querySelector('#research-results').textContent = `显示 ${count} / ${cards.length} 份报告`;
    document.querySelector('#research-empty').hidden = count !== 0;
    if (syncUrl) {
      const url = new URL(location.href);
      for (const [name, value] of [['search', search.value], ['topic', topic.value], ['status', status.value]]) {
        if (value) url.searchParams.set(name, value);
        else url.searchParams.delete(name);
      }
      history.replaceState(null, '', url);
    }
  }
  function readQuery() {
    const query = new URLSearchParams(location.search);
    search.value = query.get('search') || '';
    for (const [name, control] of [['topic', topic], ['status', status]]) {
      const value = query.get(name) || '';
      control.value = [...control.options].some(option => option.value === value) ? value : '';
    }
    filter(false);
  }
  function openTarget() {
    let id;
    try { id = decodeURIComponent(location.hash.slice(1)); }
    catch { return; }
    const card = byId.get(id);
    if (!card) return;
    if (card.hidden) {
      search.value = topic.value = status.value = '';
      filter();
    }
    const report = card.querySelector('.proposal-report');
    if (report) report.open = true;
    requestAnimationFrame(() => card.scrollIntoView({block:'start'}));
  }
  form.addEventListener('submit', event => event.preventDefault());
  form.addEventListener('reset', () => setTimeout(() => filter(), 0));
  search.addEventListener('input', () => filter());
  topic.addEventListener('change', () => filter());
  status.addEventListener('change', () => filter());
  window.addEventListener('hashchange', openTarget);
  window.addEventListener('popstate', () => { readQuery(); openTarget(); });
  document.addEventListener('click', event => {
    const blueprint = event.target.closest('[data-blueprint]');
    if (blueprint) {
      event.preventDefault();
      if (window.parent !== window) window.hgraph?.navigate(blueprint.dataset.blueprint);
      else window.open('../#/Kervaire126#' + encodeURIComponent(blueprint.dataset.blueprint), '_blank', 'noopener');
    }
    const link = event.target.closest('.research-permalink');
    if (link && link.hash === location.hash) {
      event.preventDefault();
      openTarget();
    }
  });
  readQuery();
  openTarget();
  window.hgraph?.ready();
})();
