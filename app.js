'use strict';

// ── State ──────────────────────────────────────────────────────────────────
let files         = [];          // { name: string, getContent: () => Promise<ArrayBuffer>, folderOverride?: string }
let csvMap        = new Map();   // basename → new basename
let mode          = 'rules';     // 'rules' | 'csv'
let selectedNames = new Set();   // filenames currently selected
let filterQuery   = '';          // current search filter string
let sortMode      = 'name-asc';  // current sort mode
const NOW         = new Date();  // snapshot date/time for the session

const ZIP_SIZE_LIMIT    = 500 * 1024 * 1024;  // 500 MB compressed
const UNCOMPRESSED_WARN = 200 * 1024 * 1024;  // 200 MB uncompressed total
const FILE_CAP          = 2000;
const PREVIEW_CAP       = 500;
const CSV_LIMIT         = 1 * 1024 * 1024;    // 1 MB

// ── DOM refs ───────────────────────────────────────────────────────────────
const fileDrop    = document.getElementById('file-drop');
const fileInput   = document.getElementById('file-input');
const fileBrowse  = document.getElementById('file-browse');
const previewTbody = document.getElementById('preview-tbody');
const fileBadge   = document.getElementById('file-badge');
const clearBtn    = document.getElementById('clear-btn');
const downloadBtn = document.getElementById('download-btn');
const dupeWarn    = document.getElementById('dupe-warning');
const csvDrop     = document.getElementById('csv-drop');
const csvInput    = document.getElementById('csv-input');
const csvBrowse   = document.getElementById('csv-browse');
const csvText     = document.getElementById('csv-text');
const csvApply    = document.getElementById('csv-apply');
const csvStatus   = document.getElementById('csv-status');
const fileStatus      = document.getElementById('file-status');
const limitInfoBtn    = document.getElementById('limit-info-btn');
const limitInfo       = document.getElementById('limit-info');
const selectionBar    = document.getElementById('selection-bar');
const selectionCount  = document.getElementById('selection-count');
const selFolderBtn    = document.getElementById('sel-folder-btn');
const selUnfolderBtn  = document.getElementById('sel-unfolder-btn');
const selDeleteBtn    = document.getElementById('sel-delete-btn');
const folderInputWrap = document.getElementById('folder-input-wrap');
const folderInput     = document.getElementById('folder-input');
const folderConfirmBtn = document.getElementById('folder-confirm-btn');
const folderCancelBtn  = document.getElementById('folder-cancel-btn');
const selectAll       = document.getElementById('select-all');
const fileSearch      = document.getElementById('file-search');
const fileSort        = document.getElementById('file-sort');

function showFileError(msg)   { fileStatus.textContent = msg; fileStatus.className = 'file-status error'; }
function showFileWarning(msg) { fileStatus.textContent = msg; fileStatus.className = 'file-status warning'; }
function clearFileStatus()    { fileStatus.className = 'file-status hidden'; }

function debounce(fn, ms) {
  let t;
  return (...args) => { clearTimeout(t); t = setTimeout(() => fn(...args), ms); };
}
const debouncedUpdatePreview = debounce(updatePreview, 120);

// ── Helpers ────────────────────────────────────────────────────────────────

function splitName(fullPath) {
  const lastSlash = Math.max(fullPath.lastIndexOf('/'), fullPath.lastIndexOf('\\'));
  const dir  = lastSlash >= 0 ? fullPath.slice(0, lastSlash + 1) : '';
  const base = lastSlash >= 0 ? fullPath.slice(lastSlash + 1)   : fullPath;
  const dot  = base.lastIndexOf('.');
  if (dot <= 0) return { dir, name: base, ext: '' };
  return { dir, name: base.slice(0, dot), ext: base.slice(dot) };
}

function esc(str) {
  return str.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
}

function v(id)    { return document.getElementById(id).value; }
function cb(id)   { return document.getElementById(id).checked; }
function num(id, def = 0) { return parseInt(v(id), 10) || def; }

// Apply a string transform to name, ext, or both.
// fn receives the bare string (no leading dot on ext).
function applyScope(name, ext, scope, fn) {
  if (scope === 'name' || scope === 'both') {
    name = fn(name);
  }
  if ((scope === 'ext' || scope === 'both') && ext) {
    ext = '.' + fn(ext.slice(1));
  }
  return { name, ext };
}

// ── Rule functions (applied in order 1–7) ─────────────────────────────────

function ruleTrim(name, ext) {
  if (!cb('trim-on')) return { name, ext };

  let n = name;
  if (cb('trim-lead'))  n = n.trimStart();
  if (cb('trim-trail')) n = n.trimEnd();

  const fromStart = num('trim-start');
  const fromEnd   = num('trim-end');
  if (fromStart > 0) n = n.slice(fromStart);
  if (fromEnd   > 0 && fromEnd < n.length) n = n.slice(0, n.length - fromEnd);

  if (cb('trim-spaces')) n = n.replace(/\s+/g, '');

  return { name: n, ext };
}

function ruleFindReplace(name, ext) {
  if (!cb('fr-on')) return { name, ext };

  const find = v('fr-find');
  if (!find) return { name, ext };

  const isRegex       = cb('fr-regex');
  const caseSensitive = cb('fr-case');
  const wholeWord     = cb('fr-word');
  const replace       = v('fr-replace');
  const scope         = v('fr-scope');
  const before        = v('fr-before');
  const after         = v('fr-after');
  const maxRepRaw     = v('fr-maxrep');
  const maxRep        = maxRepRaw === '' ? Infinity : (parseInt(maxRepRaw, 10) || 1);
  const dir           = v('fr-dir');

  function escRe(s) { return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'); }

  function expandReplacement(tpl, wholeMatch, ...groups) {
    return tpl.replace(/\$(\$|&|\d+)/g, (_, token) => {
      if (token === '$') return '$';
      if (token === '&') return wholeMatch;
      const n = parseInt(token, 10);
      return (n >= 1 && n <= groups.length) ? (groups[n - 1] ?? '') : `$${token}`;
    });
  }

  function doReplace(str) {
    try {
      const flags = 'g' + (caseSensitive ? '' : 'i');

      let core = isRegex ? find : escRe(find);
      if (wholeWord) core = `\\b${core}\\b`;

      const lb = before ? `(?<=${isRegex ? before : escRe(before)})` : '';
      const la = after  ? `(?=${isRegex  ? after  : escRe(after)})`  : '';
      const re = new RegExp(lb + core + la, flags);

      if (maxRep === Infinity) {
        return str.replace(re, replace);
      }

      const matches = [...str.matchAll(re)];
      const chosen  = dir === 'rtl' ? matches.slice(-maxRep) : matches.slice(0, maxRep);
      const replaceAt = new Set(chosen.map(m => m.index));
      return str.replace(re, (wholeMatch, ...rest) => {
        const offset = rest[rest.length - 2];
        if (replaceAt.has(offset)) {
          const groups = rest.slice(0, rest.length - 2);
          return expandReplacement(replace, wholeMatch, ...groups);
        }
        return wholeMatch;
      });
    } catch {
      return str;
    }
  }

  // When context fields are set, run on the full basename so the lookahead/lookbehind
  // can reference text across the name/extension boundary
  if (before || after) {
    const { name: n, ext: e } = splitName(doReplace(name + ext));
    return { name: n, ext: e };
  }
  return applyScope(name, ext, scope, doReplace);
}

function ruleCase(name, ext) {
  if (!cb('case-on')) return { name, ext };

  const type  = v('case-type');
  const scope = v('case-scope');

  function doCase(str) {
    switch (type) {
      case 'lower':    return str.toLowerCase();
      case 'upper':    return str.toUpperCase();
      case 'title':
        // lowercase everything, then capitalise first letter after word-boundary separators
        return str.toLowerCase().replace(/(^|[\s\-_.])[a-z]/g, m => m.toUpperCase());
      case 'sentence': return str.charAt(0).toUpperCase() + str.slice(1).toLowerCase();
      default: return str;
    }
  }

  return applyScope(name, ext, scope, doCase);
}

function ruleInsert(name, ext) {
  if (!cb('ins-on')) return { name, ext };

  const text    = v('ins-text');
  if (!text) return { name, ext };

  const pos     = num('ins-pos');
  const fromEnd = cb('ins-fromend');
  const scope   = v('ins-scope');

  function doInsert(str) {
    const idx = fromEnd
      ? Math.max(0, str.length - pos)
      : Math.min(pos, str.length);
    return str.slice(0, idx) + text + str.slice(idx);
  }

  return applyScope(name, ext, scope, doInsert);
}

function rulePrefixSuffix(name, ext) {
  if (!cb('ps-on')) return { name, ext };
  return {
    name: v('ps-prefix') + name + v('ps-suffix'),
    ext,
  };
}

function ruleDate(name, ext) {
  if (!cb('date-on')) return { name, ext };

  const fmt = v('date-fmt');
  const pos = v('date-pos');
  const sep = v('date-sep');

  const y  = NOW.getFullYear();
  const mo = String(NOW.getMonth() + 1).padStart(2, '0');
  const d  = String(NOW.getDate()).padStart(2, '0');
  const h  = String(NOW.getHours()).padStart(2, '0');
  const mi = String(NOW.getMinutes()).padStart(2, '0');
  const s  = String(NOW.getSeconds()).padStart(2, '0');

  const dateStr = fmt
    .replace('YYYY', y)
    .replace('YY',   String(y).slice(-2))
    .replace('MM', mo).replace('DD', d)
    .replace('HH', h) .replace('mm', mi).replace('ss', s);

  return {
    name: pos === 'prefix' ? dateStr + sep + name : name + sep + dateStr,
    ext,
  };
}

function ruleCounter(name, ext, index) {
  if (!cb('ctr-on')) return { name, ext };

  const start = num('ctr-start', 1);
  const step  = num('ctr-step',  1);
  const pad   = Math.max(1, num('ctr-pad', 1));
  const sep   = v('ctr-sep');
  const pos   = v('ctr-pos');

  const numStr = String(start + index * step).padStart(pad, '0');

  return {
    name: pos === 'prefix' ? numStr + sep + name : name + sep + numStr,
    ext,
  };
}

// ── Core rename ────────────────────────────────────────────────────────────

function applyRules(fullPath, index) {
  let { dir, name, ext } = splitName(fullPath);

  ({ name, ext } = ruleTrim(name, ext));
  ({ name, ext } = ruleFindReplace(name, ext));
  ({ name, ext } = ruleCase(name, ext));
  ({ name, ext } = ruleInsert(name, ext));
  ({ name, ext } = rulePrefixSuffix(name, ext));
  ({ name, ext } = ruleDate(name, ext));
  ({ name, ext } = ruleCounter(name, ext, index));

  return dir + name + ext;
}

function csvNewName(fullPath) {
  const { dir, name, ext } = splitName(fullPath);
  const base = name + ext;
  return dir + (csvMap.has(base) ? csvMap.get(base) : base);
}

function getNewName(fullPath, index) {
  return mode === 'rules' ? applyRules(fullPath, index) : csvNewName(fullPath);
}

// ── Preview helpers ────────────────────────────────────────────────────────

function getFilteredSorted() {
  const q = filterQuery.toLowerCase();
  let result = files.map((f, i) => ({ ...f, originalIndex: i, newName: getNewName(f.name, i) }));
  if (q) result = result.filter(f =>
    f.name.toLowerCase().includes(q) || f.newName.toLowerCase().includes(q)
  );
  if (sortMode === 'name-desc') {
    result.sort((a, b) => b.name.localeCompare(a.name));
  } else if (sortMode === 'ext') {
    result.sort((a, b) => {
      const ea = a.name.split('.').pop() ?? '';
      const eb = b.name.split('.').pop() ?? '';
      return ea.localeCompare(eb) || a.name.localeCompare(b.name);
    });
  } else if (sortMode === 'changed') {
    result = result.filter(f => f.newName !== f.name);
  }
  return result;
}

function updateSelectionBar() {
  const count = selectedNames.size;
  if (count === 0) {
    selectionBar.classList.add('hidden');
    folderInputWrap.classList.add('hidden');
    return;
  }
  selectionBar.classList.remove('hidden');
  selectionCount.textContent = `${count} file${count !== 1 ? 's' : ''} selected`;
  const selFiles  = files.filter(f => selectedNames.has(f.name));
  const hasFolded = selFiles.some(f => f.folderOverride);
  selUnfolderBtn.classList.toggle('hidden', !hasFolded);
}

// ── Preview ────────────────────────────────────────────────────────────────

function updatePreview() {
  const totalCount = files.length;
  const filtered   = getFilteredSorted();
  const showing    = filtered.length;
  const isFiltered = filterQuery !== '' || sortMode === 'changed';

  fileBadge.textContent = isFiltered
    ? `${showing} / ${totalCount} file${totalCount !== 1 ? 's' : ''}`
    : `${totalCount} file${totalCount !== 1 ? 's' : ''}`;

  if (totalCount === 0) {
    previewTbody.innerHTML = '<tr class="empty-row"><td colspan="4">Upload files to see a preview</td></tr>';
    downloadBtn.disabled = true;
    dupeWarn.classList.add('hidden');
    selectAll.checked = false;
    selectAll.indeterminate = false;
    updateSelectionBar();
    return;
  }

  downloadBtn.disabled = false;

  // Duplicate detection across ALL files (not just visible)
  const allNewNames = files.map(({ name }, i) => getNewName(name, i));
  const seen = new Set(), dupes = new Set();
  for (const n of allNewNames) { if (seen.has(n)) dupes.add(n); seen.add(n); }
  dupeWarn.classList.toggle('hidden', dupes.size === 0);

  const visibleSlice = filtered.slice(0, PREVIEW_CAP);
  const overflow = filtered.length > PREVIEW_CAP
    ? `<tr class="empty-row"><td colspan="4">…and ${filtered.length - PREVIEW_CAP} more files not shown</td></tr>`
    : '';

  previewTbody.innerHTML = visibleSlice.map(({ name, originalIndex, newName, folderOverride }) => {
    const changed    = newName !== name;
    const isDupe     = dupes.has(newName);
    const isSelected = selectedNames.has(name);
    const cls        = isDupe ? 'dupe' : (changed ? 'changed' : '');
    const displayNew = folderOverride
      ? `<span class="folder-prefix">${esc(folderOverride)}/</span>${esc(newName)}`
      : esc(newName);
    return `<tr${cls ? ` class="${cls}"` : ''}>
      <td class="col-check"><input type="checkbox" class="row-check" data-name="${esc(name)}" ${isSelected ? 'checked' : ''}></td>
      <td title="${esc(name)}">${esc(name)}</td>
      <td title="${folderOverride ? esc(folderOverride + '/' + newName) : esc(newName)}" class="${changed ? 'new-name' : ''}">${displayNew}</td>
      <td><button class="del-btn" data-idx="${originalIndex}" title="Remove this file">×</button></td>
    </tr>`;
  }).join('') + overflow;

  // Sync select-all header checkbox
  const visibleNames = visibleSlice.map(f => f.name);
  const allChecked   = visibleNames.length > 0 && visibleNames.every(n => selectedNames.has(n));
  const someChecked  = visibleNames.some(n => selectedNames.has(n));
  selectAll.checked       = allChecked;
  selectAll.indeterminate = someChecked && !allChecked;

  updateSelectionBar();
}

// ── File loading ───────────────────────────────────────────────────────────

async function loadFiles(fileList) {
  const loaded = [];
  clearFileStatus();

  for (const file of fileList) {
    if (file.name.toLowerCase().endsWith('.zip')) {
      if (file.size > ZIP_SIZE_LIMIT) {
        showFileError(`"${file.name}" is too large (${(file.size / 1024 / 1024).toFixed(0)} MB). Browsers load files entirely into memory, so ZIPs over 500 MB may cause the tab to crash. Try splitting your archive into smaller ZIPs and processing them separately.`);
        continue;
      }
      try {
        const zip = await JSZip.loadAsync(file);

        let estimatedBytes = 0;
        zip.forEach((_, e) => { estimatedBytes += e._data?.uncompressedSize ?? 0; });
        if (estimatedBytes > UNCOMPRESSED_WARN) {
          showFileWarning(`ZIP contains ~${(estimatedBytes / 1024 / 1024).toFixed(0)} MB of uncompressed content. The browser holds all of this in memory while renaming — the download step may be slow or unresponsive. For best results, split large archives into smaller ZIPs under 200 MB.`);
        }

        zip.forEach((path, entry) => {
          if (!entry.dir && files.length + loaded.length < FILE_CAP) {
            loaded.push({ name: path, getContent: () => entry.async('arraybuffer') });
          }
        });
      } catch (err) {
        showFileError(`Could not read "${file.name}": ${err.message}`);
      }
    } else {
      if (files.length + loaded.length < FILE_CAP) {
        loaded.push({ name: file.name, getContent: () => file.arrayBuffer() });
      }
    }
  }

  const existingNames = new Set(files.map(f => f.name));
  const newUnique = loaded.filter(f => !existingNames.has(f.name));
  files = [...files, ...newUnique].sort((a, b) => a.name.localeCompare(b.name));

  if (files.length >= FILE_CAP) {
    showFileWarning('File limit reached (2,000 files). Remove individual files to make room for more.');
  }

  updatePreview();
}

// ── CSV parsing ────────────────────────────────────────────────────────────

function parseAndApplyCSV(text) {
  if (text.length > CSV_LIMIT) {
    csvStatus.textContent = 'CSV is too large (limit: 1 MB). A mapping file this size is unusual — consider trimming unused rows, or split your files into smaller batches with a separate CSV each.';
    csvStatus.className = 'csv-status error';
    return;
  }

  const map = new Map();
  let errors = 0;

  for (const raw of text.split('\n')) {
    const line = raw.trim();
    if (!line) continue;

    // Naive CSV split on first comma; strip optional surrounding quotes
    const comma = line.indexOf(',');
    if (comma < 0) { errors++; continue; }

    const strip = s => s.trim().replace(/^["']|["']$/g, '');
    const orig  = strip(line.slice(0, comma));
    const next  = strip(line.slice(comma + 1));

    if (orig && next) map.set(orig, next);
    else errors++;
  }

  csvMap = map;

  const msg = `${map.size} mapping${map.size !== 1 ? 's' : ''} loaded` +
              (errors ? `, ${errors} invalid row${errors !== 1 ? 's' : ''} skipped` : '');
  csvStatus.textContent = msg;
  csvStatus.className   = 'csv-status ' + (map.size > 0 ? 'success' : 'error');

  updatePreview();
}

// ── Download ───────────────────────────────────────────────────────────────

async function downloadZip() {
  if (!files.length) return;

  const exportFiles = selectedNames.size > 0
    ? files.filter(f => selectedNames.has(f.name))
    : files;
  if (!exportFiles.length) return;

  downloadBtn.disabled = true;
  downloadBtn.textContent = 'Processing…';

  try {
    const zip = new JSZip();

    for (let i = 0; i < exportFiles.length; i++) {
      const f       = exportFiles[i];
      const renamed = getNewName(f.name, i);
      const outPath = f.folderOverride
        ? `${f.folderOverride}/${renamed.split('/').pop()}`
        : renamed;
      zip.file(outPath, f.getContent());
    }

    const blob = await zip.generateAsync(
      { type: 'blob', compression: 'DEFLATE', compressionOptions: { level: 6 } },
      ({ percent }) => { downloadBtn.textContent = `Processing… ${Math.round(percent)}%`; }
    );

    const url = URL.createObjectURL(blob);
    const a   = Object.assign(document.createElement('a'), { href: url, download: 'renamed.zip' });
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  } finally {
    downloadBtn.disabled = false;
    downloadBtn.textContent = 'Rename & Download ZIP';
  }
}

// ── Drag-and-drop helper ───────────────────────────────────────────────────

function makeDrop(zone, onFiles) {
  zone.addEventListener('dragover', e => {
    e.preventDefault();
    zone.classList.add('drag-over');
  });
  zone.addEventListener('dragleave', e => {
    if (!zone.contains(e.relatedTarget)) zone.classList.remove('drag-over');
  });
  zone.addEventListener('drop', e => {
    e.preventDefault();
    zone.classList.remove('drag-over');
    onFiles([...e.dataTransfer.files]);
  });
}

// ── Init ───────────────────────────────────────────────────────────────────

document.addEventListener('DOMContentLoaded', () => {

  // Limit info toggle
  limitInfoBtn.addEventListener('click', e => {
    e.stopPropagation();
    limitInfo.classList.toggle('hidden');
  });
  document.addEventListener('click', () => limitInfo.classList.add('hidden'));

  // File drop zone
  makeDrop(fileDrop, loadFiles);
  fileDrop.addEventListener('click', () => fileInput.click());
  fileBrowse.addEventListener('click', e => { e.stopPropagation(); fileInput.click(); });
  fileInput.addEventListener('change', () => { loadFiles([...fileInput.files]); fileInput.value = ''; });
  clearBtn.addEventListener('click', () => { files = []; selectedNames.clear(); clearFileStatus(); updatePreview(); });

  previewTbody.addEventListener('click', e => {
    const btn = e.target.closest('.del-btn');
    if (!btn) return;
    const idx = parseInt(btn.dataset.idx, 10);
    selectedNames.delete(files[idx].name);
    files.splice(idx, 1);
    updatePreview();
  });

  // Search and sort
  fileSearch.addEventListener('input', () => { filterQuery = fileSearch.value; updatePreview(); });
  fileSort.addEventListener('change',  () => { sortMode = fileSort.value; updatePreview(); });

  // Select all (acts on currently visible filtered rows)
  selectAll.addEventListener('change', () => {
    const visible = getFilteredSorted().slice(0, PREVIEW_CAP);
    if (selectAll.checked) visible.forEach(f => selectedNames.add(f.name));
    else                   visible.forEach(f => selectedNames.delete(f.name));
    updatePreview();
  });

  // Row checkbox delegation — update Set without full re-render
  previewTbody.addEventListener('change', e => {
    const cb = e.target.closest('.row-check');
    if (!cb) return;
    if (cb.checked) selectedNames.add(cb.dataset.name);
    else            selectedNames.delete(cb.dataset.name);
    updateSelectionBar();
    const allBoxes = [...previewTbody.querySelectorAll('.row-check')];
    const allChk   = allBoxes.every(c => c.checked);
    const someChk  = allBoxes.some(c => c.checked);
    selectAll.checked       = allChk;
    selectAll.indeterminate = someChk && !allChk;
  });

  // Delete selected
  selDeleteBtn.addEventListener('click', () => {
    files = files.filter(f => !selectedNames.has(f.name));
    selectedNames.clear();
    updatePreview();
  });

  // Move to folder
  selFolderBtn.addEventListener('click', () => {
    folderInputWrap.classList.remove('hidden');
    folderInput.focus();
  });
  folderCancelBtn.addEventListener('click', () => {
    folderInputWrap.classList.add('hidden');
    folderInput.value = '';
  });
  folderConfirmBtn.addEventListener('click', () => {
    const folder = folderInput.value.trim().replace(/^\/+|\/+$/g, '');
    if (!folder) return;
    files.forEach(f => { if (selectedNames.has(f.name)) f.folderOverride = folder; });
    folderInputWrap.classList.add('hidden');
    folderInput.value = '';
    updatePreview();
  });
  folderInput.addEventListener('keydown', e => {
    if (e.key === 'Enter')  folderConfirmBtn.click();
    if (e.key === 'Escape') folderCancelBtn.click();
  });

  // Remove from folder
  selUnfolderBtn.addEventListener('click', () => {
    files.forEach(f => { if (selectedNames.has(f.name)) delete f.folderOverride; });
    updatePreview();
  });

  // CSV drop zone
  makeDrop(csvDrop, async drops => {
    const csv = drops.find(f => f.name.toLowerCase().endsWith('.csv'));
    if (csv) {
      if (csv.size > CSV_LIMIT) {
        csvStatus.textContent = `CSV file is too large (${(csv.size / 1024).toFixed(0)} KB, limit: 1 MB). Consider trimming unused rows, or split your files into smaller batches with a separate CSV each.`;
        csvStatus.className = 'csv-status error';
        return;
      }
      csvText.value = await csv.text();
      parseAndApplyCSV(csvText.value);
    }
  });
  csvDrop.addEventListener('click', () => csvInput.click());
  csvBrowse.addEventListener('click', e => { e.stopPropagation(); csvInput.click(); });
  csvInput.addEventListener('change', async () => {
    const csv = csvInput.files[0];
    if (csv) {
      if (csv.size > CSV_LIMIT) {
        csvStatus.textContent = `CSV file is too large (${(csv.size / 1024).toFixed(0)} KB, limit: 1 MB). Consider trimming unused rows, or split your files into smaller batches with a separate CSV each.`;
        csvStatus.className = 'csv-status error';
        csvInput.value = '';
        return;
      }
      csvText.value = await csv.text();
      parseAndApplyCSV(csvText.value);
    }
    csvInput.value = '';
  });
  csvApply.addEventListener('click', () => parseAndApplyCSV(csvText.value));

  // Tab switching
  document.querySelectorAll('.tab').forEach(tab => {
    tab.addEventListener('click', () => {
      document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
      document.querySelectorAll('.tab-panel').forEach(p => p.classList.remove('active'));
      tab.classList.add('active');
      document.getElementById('tab-' + tab.dataset.tab).classList.add('active');
      mode = tab.dataset.tab;
      updatePreview();
    });
  });

  // Rule enable/disable toggle (visual state + preview)
  document.querySelectorAll('.rule-check input[type="checkbox"]').forEach(checkbox => {
    const card = checkbox.closest('.rule-card');
    const sync = () => card.classList.toggle('enabled', checkbox.checked);
    checkbox.addEventListener('change', () => { sync(); updatePreview(); });
    sync();
  });

  // Any input change inside the rules panel → refresh preview
  document.getElementById('tab-rules').addEventListener('input',  debouncedUpdatePreview);
  document.getElementById('tab-rules').addEventListener('change', debouncedUpdatePreview);

  // Download
  downloadBtn.addEventListener('click', downloadZip);

  updatePreview();
});
