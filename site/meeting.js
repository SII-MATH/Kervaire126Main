(() => {
  'use strict';
  const rows = [...document.querySelectorAll('tbody tr')];
  const search = document.querySelector('#task-search');
  const status = document.querySelector('#task-status');
  const followUp = new Set(['in_progress', 'to_confirm', 'to_discuss', 'to_verify']);
  const validStatuses = new Set([...status.options].map(option => option.value));
  const metrics = [...document.querySelectorAll('[data-filter]')];

  function filter() {
    const query = search.value.trim().toLocaleLowerCase();
    let count = 0;
    for (const row of rows) {
      const matches = status.value === 'all' || row.dataset.status === status.value ||
        (status.value === 'follow_up' && followUp.has(row.dataset.status));
      row.hidden = !matches || !row.dataset.search.toLocaleLowerCase().includes(query);
      if (!row.hidden) count++;
    }
    document.querySelector('#result-count').textContent = `显示 ${count} / ${rows.length} 项`;
    document.querySelector('#no-results').hidden = count !== 0;
    document.querySelector('.task-table').hidden = count === 0;
    for (const metric of metrics) metric.setAttribute('aria-pressed', String(metric.dataset.filter === status.value));
    const url = new URL(location.href);
    if (document.getElementById(url.hash.slice(1))?.hidden) url.hash = '';
    for (const [key, value] of [['search', search.value], ['status', status.value === 'all' ? '' : status.value]]) {
      if (value) url.searchParams.set(key, value); else url.searchParams.delete(key);
    }
    history.replaceState(null, '', url);
  }

  function reset() { search.value = ''; status.value = 'all'; filter(); }
  function focusTask(identity) {
    const target = document.getElementById(identity);
    if (!target?.matches('tbody tr')) return;
    if (target.hidden) reset();
    for (const row of rows) row.classList.toggle('task-focused', row === target);
    target.scrollIntoView({block:'center'});
    target.focus({preventScroll:true});
  }

  document.querySelector('#meeting-filters').addEventListener('submit', event => event.preventDefault());
  search.addEventListener('input', filter);
  status.addEventListener('change', filter);
  document.querySelector('#reset-filters').addEventListener('click', reset);
  document.querySelector('[data-reset]').addEventListener('click', reset);
  for (const metric of metrics) metric.addEventListener('click', () => {
    search.value = ''; status.value = metric.dataset.filter; filter();
  });
  document.addEventListener('click', event => {
    const link = event.target.closest('a[data-target]');
    if (!link || event.button !== 0 || event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
    event.preventDefault();
    const url = new URL(location.href); url.hash = link.dataset.target;
    history.replaceState(null, '', url);
    focusTask(link.dataset.target);
  });
  const parameters = new URLSearchParams(location.search);
  search.value = parameters.get('search') || '';
  status.value = validStatuses.has(parameters.get('status')) ? parameters.get('status') : 'all';
  filter();
  focusTask(location.hash.slice(1));
  window.addEventListener('hashchange', () => focusTask(location.hash.slice(1)));
  window.hgraph?.ready();
})();
