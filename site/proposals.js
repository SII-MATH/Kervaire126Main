(() => {
  'use strict';
  const cards = [...document.querySelectorAll('.proposal-card')];
  const search = document.querySelector('#proposal-search');
  const module = document.querySelector('#proposal-module');
  const status = document.querySelector('#proposal-status');
  const searchable = new Map(cards.map(card => [card, card.textContent.toLocaleLowerCase()]));
  document.querySelector('.proposal-filters').addEventListener('submit', event => event.preventDefault());
  for (const name of [...new Set(cards.map(card => card.dataset.module))].sort()) {
    const option = document.createElement('option');
    option.value = name;
    option.textContent = name === 'Computation' ? 'Computation（历史归属）' : name;
    module.append(option);
  }
  function filter() {
    const words = search.value.trim().toLocaleLowerCase().split(/\s+/).filter(Boolean);
    for (const card of cards) {
      card.hidden = Boolean((module.value && card.dataset.module !== module.value) ||
        (status.value && card.dataset.status !== status.value) ||
        words.some(word => !searchable.get(card).includes(word)));
    }
    const visible = cards.filter(card => !card.hidden).length;
    document.querySelector('#proposal-results').textContent = `显示 ${visible} / ${cards.length} 份报告`;
    document.querySelector('#proposal-empty').hidden = visible !== 0;
  }
  search.addEventListener('input', filter);
  module.addEventListener('change', filter);
  status.addEventListener('change', filter);
  document.querySelector('.proposal-filters').addEventListener('reset', () => setTimeout(filter, 0));
  const query = new URLSearchParams(window.interfaceInitialFilters || location.search);
  search.value = query.get('search') || '';
  if ([...module.options].some(option => option.value === query.get('module'))) module.value = query.get('module');
  window.addEventListener('interfaces:filters', event => {
    if ('search' in event.detail) search.value = event.detail.search;
    if ('module' in event.detail) module.value = event.detail.module;
    filter();
  });
  filter();
  document.addEventListener('click', event => {
    const link = event.target.closest('[data-blueprint]');
    if (link) {
      event.preventDefault();
      if (window.parent !== window) window.hgraph.navigate(link.dataset.blueprint);
      else window.open('../#/Kervaire126#' + encodeURIComponent(link.dataset.blueprint), '_blank', 'noopener');
    }
    const button = event.target.closest('[data-feedback]');
    if (button) {
      document.querySelector('#proposal-review-id').textContent = button.dataset.feedback;
      document.querySelector('#proposal-feedback').value = '';
      document.querySelector('#proposal-feedback-status').textContent = '';
      document.querySelector('#proposal-review').showModal();
    }
  });
  function feedback() {
    const id = document.querySelector('#proposal-review-id').textContent;
    const text = document.querySelector('#proposal-feedback').value.trim();
    if (!text) {
      document.querySelector('#proposal-feedback-status').textContent = '请先填写具体审阅意见。';
      return null;
    }
    return {id, text: `接口提案审阅反馈\nproposal: ${id}\n\n${text}\n\n请将以上人审意见和明确授权范围回写到该提案的 report.md；保留未批准范围与证据边界。\n`};
  }
  document.querySelector('#proposal-copy').addEventListener('click', async () => {
    const record = feedback();
    if (!record) return;
    try {
      await navigator.clipboard.writeText(record.text);
      document.querySelector('#proposal-feedback-status').textContent = '反馈已复制；交给 agent 回写后才会更新报告。';
    } catch {
      document.querySelector('#proposal-feedback-status').textContent = '浏览器不允许复制，请下载反馈。';
    }
  });
  document.querySelector('#proposal-download').addEventListener('click', () => {
    const record = feedback();
    if (!record) return;
    const url = URL.createObjectURL(new Blob([record.text], {type:'text/plain;charset=utf-8'}));
    const link = document.createElement('a');
    link.href = url; link.download = record.id + '-review.txt'; link.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
    document.querySelector('#proposal-feedback-status').textContent = '反馈已下载；报告状态尚未改变。';
  });
  document.addEventListener('keydown', event => {
    const dialog = document.querySelector('#proposal-review');
    if (event.key === 'Escape' && dialog.open) {
      event.preventDefault();
      dialog.close();
    }
  }, true);
  window.hgraph?.ready();
})();
