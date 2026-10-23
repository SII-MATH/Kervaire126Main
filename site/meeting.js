(() => {
  'use strict';
  const rows = [...document.querySelectorAll('tbody tr')];
  const search = document.querySelector('#task-search');
  const status = document.querySelector('#task-status');
  const category = document.querySelector('#task-category');
  const meeting = document.querySelector('#meeting-select');
  const followUp = new Set(['pending', 'in_progress', 'to_confirm', 'to_discuss', 'to_verify']);
  const validStatuses = new Set([...status.options].map(option => option.value));
  const metrics = [...document.querySelectorAll('[data-filter]')];

  function filter() {
    const query = search.value.trim().toLocaleLowerCase();
    let count = 0;
    for (const row of rows) {
      const matches = status.value === 'all' || row.dataset.status === status.value ||
        (status.value === 'follow_up' && followUp.has(row.dataset.status));
      row.hidden = !matches || !row.dataset.search.toLocaleLowerCase().includes(query) ||
        (category && category.value !== 'all' && row.dataset.category !== category.value);
      if (!row.hidden) count++;
    }
    document.querySelector('#result-count').textContent = `显示 ${count} / ${rows.length} 项`;
    document.querySelector('#no-results').hidden = count !== 0;
    document.querySelector('.task-table').hidden = count === 0;
    for (const metric of metrics) metric.setAttribute('aria-pressed', String(metric.dataset.filter === status.value));
    const url = new URL(location.href);
    if (document.getElementById(url.hash.slice(1))?.hidden) url.hash = '';
    for (const [key, value] of [['search', search.value], ['status', status.value === 'all' ? '' : status.value],
      ['category', category && category.value !== 'all' ? category.value : '']]) {
      if (value) url.searchParams.set(key, value); else url.searchParams.delete(key);
    }
    history.replaceState(null, '', url);
  }

  function reset() { search.value = ''; status.value = 'all'; if (category) category.value = 'all'; filter(); }
  function focusTask(identity) {
    const target = document.getElementById(identity);
    if (!target?.matches('tbody tr')) return;
    if (target.hidden) reset();
    const url = new URL(location.href); url.hash = identity;
    history.replaceState(null, '', url);
    for (const row of rows) row.classList.toggle('task-focused', row === target);
    target.scrollIntoView({block:'center'});
    target.focus({preventScroll:true});
  }

  document.querySelector('#meeting-filters').addEventListener('submit', event => event.preventDefault());
  search.addEventListener('input', filter);
  status.addEventListener('change', filter);
  category?.addEventListener('change', filter);
  meeting.addEventListener('change', () => { location.assign(meeting.value); });
  document.querySelector('#reset-filters').addEventListener('click', reset);
  document.querySelector('[data-reset]').addEventListener('click', reset);
  for (const metric of metrics) metric.addEventListener('click', () => {
    search.value = ''; status.value = metric.dataset.filter;
    if (category) category.value = 'all';
    filter();
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
  const legacy = [...document.querySelectorAll('[data-legacy-task]')].find(
    link => link.dataset.legacyTask === location.hash.slice(1));
  if (legacy) {
    const destination = new URL(legacy.href);
    destination.search = location.search;
    location.replace(destination);
    return;
  }
  search.value = parameters.get('search') || '';
  status.value = validStatuses.has(parameters.get('status')) ? parameters.get('status') : 'all';
  if (category) category.value = [...category.options].some(option => option.value === parameters.get('category'))
    ? parameters.get('category') : 'all';
  const initialTask = location.hash.slice(1);
  filter();
  focusTask(initialTask);
  window.addEventListener('hashchange', () => focusTask(location.hash.slice(1)));
  window.hgraph?.ready();
})();
