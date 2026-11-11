// Copyright (c) 2026 SymLean Team. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Hover content is exported from Lean at build time; no language server or network is needed.
(() => {
  const header = document.querySelector('.topbar');
  if (header) {
    const measureHeader = () => document.documentElement.style.setProperty('--header-height', `${header.offsetHeight}px`);
    measureHeader();
    new ResizeObserver(measureHeader).observe(header);
  }
  const tip = document.createElement('div');
  tip.id = 'lean-tooltip';
  tip.className = 'lean-tooltip';
  tip.setAttribute('role', 'tooltip');
  tip.hidden = true;
  const content = document.createElement('pre');
  tip.append(content);
  document.body.append(tip);
  let active = null;
  let timer;
  const hide = () => {
    clearTimeout(timer);
    active?.removeAttribute('aria-describedby');
    active = null;
    tip.hidden = true;
  };
  const later = () => { timer = setTimeout(hide, 150); };
  const position = () => {
    if (!active || tip.hidden) return;
    const box = active.getBoundingClientRect();
    if (box.bottom < 0 || box.top > innerHeight) { hide(); return; }
    const width = tip.offsetWidth;
    tip.style.left = `${Math.max(8, Math.min(box.left, innerWidth - width - 8))}px`;
    const height = tip.offsetHeight;
    tip.style.top = `${Math.max(8, box.bottom + height + 12 < innerHeight
      ? box.bottom + 8 : box.top - height - 8)}px`;
  };
  const show = (target) => {
    clearTimeout(timer);
    if (!target) return;
    active?.removeAttribute('aria-describedby');
    active = target;
    target.removeAttribute('title');
    target.setAttribute('aria-describedby', tip.id);
    content.textContent = target.dataset.leanHover;
    tip.hidden = false;
    position();
  };
  document.addEventListener('pointerover', (event) => {
    const target = event.target.closest?.('[data-lean-hover]');
    if (target && target !== active) show(target);
  });
  document.addEventListener('pointerout', (event) => {
    if (event.pointerType === 'touch') return;
    if (active?.contains(event.target) && !active.contains(event.relatedTarget)) later();
  });
  tip.addEventListener('pointerenter', () => clearTimeout(timer));
  tip.addEventListener('pointerleave', later);
  document.addEventListener('focusin', (event) => show(event.target.closest?.('[data-lean-hover]')));
  document.addEventListener('focusout', (event) => { if (active === event.target) hide(); });
  document.addEventListener('click', (event) => {
    const target = event.target.closest?.('[data-lean-hover]');
    if (target) show(target);
    else if (!tip.contains(event.target)) hide();
  });
  document.addEventListener('keydown', (event) => { if (event.key === 'Escape') hide(); });
  window.addEventListener('resize', hide);
  window.addEventListener('scroll', position, { passive: true });
})();
