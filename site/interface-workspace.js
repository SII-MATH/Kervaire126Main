(() => {
  'use strict';
  const frames = new Map();
  const parameters = new Map();
  const channel = 'kip126:interfaces';
  const buttons = [...document.querySelectorAll('[data-section]')];
  let active;
  function sendFilters(section) {
    const values = parameters.get(section);
    if (values) frames.get(section)?.contentWindow.postMessage({channel, version:1, type:'filters', parameters:values}, location.origin);
  }
  function show(section, values = {}) {
    if (!['baselines','proposals'].includes(section)) return;
    active = section;
    if (Object.keys(values).length) parameters.set(section, values);
    if (!frames.has(section)) {
      const frame = document.createElement('iframe');
      const query = new URLSearchParams({...values, embedded:'1'});
      frame.src = (section === 'baselines' ? 'baselines.html' : '../proposals/index.html') + '?' + query;
      frame.title = section === 'baselines' ? 'Baselines' : 'Proposals';
      frame.id = section === 'baselines' ? 'baseline-panel' : 'proposal-panel';
      frame.setAttribute('role','tabpanel');
      frame.setAttribute('aria-labelledby', section === 'baselines' ? 'baseline-tab' : 'proposal-tab');
      frame.addEventListener('load', () => sendFilters(section));
      frames.set(section,frame); document.querySelector('.interface-panels').append(frame);
    } else if (Object.keys(values).length) sendFilters(section);
    for (const [name,frame] of frames) frame.hidden = name !== section;
    for (const button of buttons) {
      button.setAttribute('aria-selected',String(button.dataset.section === section));
      button.tabIndex = button.dataset.section === section ? 0 : -1;
    }
  }
  for (const button of buttons) {
    button.addEventListener('click', () => show(button.dataset.section));
    button.addEventListener('keydown', event => {
      if (!['ArrowLeft','ArrowRight','Home','End'].includes(event.key)) return;
      event.preventDefault(); const index = buttons.indexOf(button);
      const target = event.key === 'Home' ? buttons[0] : event.key === 'End' ? buttons.at(-1) : buttons[(index + 1) % 2];
      show(target.dataset.section); target.focus();
    });
  }
  window.addEventListener('message', event => {
    if (event.origin !== location.origin || event.source !== frames.get(active)?.contentWindow) return;
    const data = event.data;
    if (data?.version !== 1) return;
    if (data.channel === channel && data.type === 'switch') {
      const values = {};
      for (const key of ['search','module']) if (typeof data.parameters?.[key] === 'string') values[key] = data.parameters[key];
      show(data.section,values);
    }
    if (data.channel === 'hgraph:custom-page') {
      if (data.type === 'close') window.hgraph?.close();
      if (data.type === 'navigate' && typeof data.locator === 'string' && data.locator) window.hgraph?.navigate(data.locator);
    }
  });
  const query = new URLSearchParams(location.search);
  const values = {};
  for (const key of ['search','module']) if (query.has(key)) values[key] = query.get(key);
  show(query.get('section') === 'proposals' ? 'proposals' : 'baselines',values);
  window.hgraph?.ready();
})();
