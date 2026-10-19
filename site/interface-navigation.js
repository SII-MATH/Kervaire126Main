(() => {
  'use strict';
  const embedded = new URLSearchParams(location.search).get('embedded') === '1' && parent !== window;
  if (embedded) document.documentElement.classList.add('interface-embedded');
  const channel = 'kip126:interfaces';
  document.addEventListener('click', event => {
    const link = event.target.closest('a[data-interface-section]');
    if (!link || event.button !== 0 || event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
    const url = new URL(link.href);
    const parameters = {};
    for (const key of ['module','search']) if (url.searchParams.has(key)) parameters[key] = url.searchParams.get(key);
    if (embedded) {
      event.preventDefault(); parent.postMessage({channel,version:1,type:'switch',section:link.dataset.interfaceSection,parameters},location.origin);
    }
  });
  window.addEventListener('message', event => {
    if (!embedded || event.origin !== location.origin || event.source !== parent || event.data?.channel !== channel || event.data.version !== 1 || event.data.type !== 'filters') return;
    const values = {};
    for (const key of ['module','search']) if (typeof event.data.parameters?.[key] === 'string') values[key] = event.data.parameters[key];
    window.interfaceInitialFilters = values;
    window.dispatchEvent(new CustomEvent('interfaces:filters',{detail:values}));
  });
})();
