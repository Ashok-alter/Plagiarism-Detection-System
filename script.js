const docs = [
  document.getElementById('doc1'),
  document.getElementById('doc2')
];
const uploadStatus = document.getElementById('uploadStatus');
const compareButton = document.getElementById('compareButton');
const perDocUploadInputs = Array.from(document.querySelectorAll('.doc-upload-input')).filter(function(input) {
  return ['0', '1'].includes(input.dataset.doc);
});
const countA = document.getElementById('countA');
const countB = document.getElementById('countB');
const algorithmSelect = document.getElementById('algorithmSelect');
const algorithmDescription = document.getElementById('algorithmDescription');
const algorithmComplexity = document.getElementById('algorithmComplexity');
const verdictBanner = document.getElementById('verdictBanner');
const verdictTitle = document.getElementById('verdictTitle');
const verdictSubtitle = document.getElementById('verdictSubtitle');
const metricSimilarity = document.getElementById('metricSimilarity');
const metricWordsA = document.getElementById('metricWordsA');
const metricWordsB = document.getElementById('metricWordsB');
const metricShared = document.getElementById('metricShared');
const highlightA = document.getElementById('highlightA');
const highlightB = document.getElementById('highlightB');
const aiReport = document.getElementById('aiReport');
const barDynamicProgramming = document.getElementById('barDynamicProgramming');
const barDivideConquer = document.getElementById('barDivideConquer');
const barGreedy = document.getElementById('barGreedy');
const barBacktracking = document.getElementById('barBacktracking');
const barBranchAndBound = document.getElementById('barBranchAndBound');
const barDynamicProgrammingLabel = document.getElementById('barDynamicProgrammingLabel');
const barDivideConquerLabel = document.getElementById('barDivideConquerLabel');
const barGreedyLabel = document.getElementById('barGreedyLabel');
const barBacktrackingLabel = document.getElementById('barBacktrackingLabel');
const barBranchAndBoundLabel = document.getElementById('barBranchAndBoundLabel');
const pipelineSteps = Array.from(document.querySelectorAll('.pipeline-step'));
const matrixTable = document.getElementById('matrixTable');
const ngramSelect = document.getElementById('ngramSelect');
const ngramSummary = document.getElementById('ngramSummary');
const sentenceTable = document.getElementById('sentenceTable');
const historyList = document.getElementById('historyList');
const clearHistoryButton = document.getElementById('clearHistory');
const downloadReportButton = document.getElementById('downloadReport');
const toggleThemeButton = document.getElementById('toggleTheme');
const liveStatus = document.getElementById('liveStatus');
const serverStatus = document.getElementById('serverStatus');
const raceToggle = document.getElementById('raceToggle');
const raceStatus = document.getElementById('raceStatus');
const visualizerMode = document.getElementById('visualizerMode');
const visualizerPrev = document.getElementById('visualizerPrev');
const visualizerNext = document.getElementById('visualizerNext');
const visualizerReset = document.getElementById('visualizerReset');
const visualizerDescription = document.getElementById('visualizerDescription');
const visualizerOutput = document.getElementById('visualizerOutput');
const stepCounter = document.getElementById('stepCounter');
const gaugeFill = document.getElementById('gaugeFill');
const gaugeValue = document.getElementById('gaugeValue');
let visualizerSteps = [];
let visualizerIndex = 0;
let isRemoteUpdate = false;

const algorithmData = {
  'dynamic-programming': {
    label: 'Dynamic Programming',
    description: 'Uses DP-based edit distance and shared subproblem structure to compare documents step by step.',
    complexity: 'O(n × m)'
  },
  'divide-conquer': {
    label: 'Divide & Conquer',
    description: 'Uses divide-and-conquer style matching by sorting token sets and searching with binary search heuristics.',
    complexity: 'O(n log n)'
  },
  greedy: {
    label: 'Greedy Method',
    description: 'Uses greedy sequence selection to maximize immediate matches and build a fast similarity estimate.',
    complexity: 'O(n)'
  },
  backtracking: {
    label: 'Backtracking',
    description: 'Explores alternative match sequences with backtracking to illustrate search and pruning choices.',
    complexity: 'O(2^n) worst-case'
  },
  'branch-and-bound': {
    label: 'Branch & Bound',
    description: 'Uses branch-and-bound style pruning and score bounding to identify strong matching candidates.',
    complexity: 'O(2^n) worst-case'
  }
};

function normalizeText(text) {
  return String(text)
    .trim()
    .replace(/[\n\r]+/g, ' ')
    .replace(/[“”‘’`]/g, "'")
    .replace(/[^0-9a-zA-Z\s]+/g, ' ')
    .toLowerCase();
}

function tokenizeWords(text) {
  return normalizeText(text).split(/\s+/).filter(Boolean);
}

function uniqueWords(words) {
  return [...new Set(words)];
}

function buildFrequencyMap(words) {
  return words.reduce(function(map, word) {
    map[word] = (map[word] || 0) + 1;
    return map;
  }, {});
}

function kmpSearch(text, pattern) {
  var n = text.length;
  var m = pattern.length;
  if (m === 0) return 0;
  var lps = Array(m).fill(0);
  var len = 0;
  for (var i = 1; i < m;) {
    if (pattern[i] === pattern[len]) {
      len += 1;
      lps[i++] = len;
    } else if (len !== 0) {
      len = lps[len - 1];
    } else {
      lps[i++] = 0;
    }
  }
  var count = 0;
  var i = 0;
  var j = 0;
  while (i < n) {
    if (pattern[j] === text[i]) {
      i += 1;
      j += 1;
    }
    if (j === m) {
      count += 1;
      j = lps[j - 1];
    } else if (i < n && pattern[j] !== text[i]) {
      if (j !== 0) {
        j = lps[j - 1];
      } else {
        i += 1;
      }
    }
  }
  return count;
}

function rollingHashMatches(source, target, length) {
  if (length === 0 || source.length < length || target.length < length) return 0;
  var base = 257;
  var mod = 1000000007;
  function computeHash(arr) {
    return arr.reduce(function(hash, token) {
      for (var i = 0; i < token.length; i += 1) {
        hash = (hash * base + token.charCodeAt(i)) % mod;
      }
      return hash;
    }, 0);
  }
  var sourceHashes = new Set();
  for (var i = 0; i + length <= source.length; i += 1) {
    sourceHashes.add(computeHash(source.slice(i, i + length)));
  }
  var matches = 0;
  for (var j = 0; j + length <= target.length; j += 1) {
    var hashValue = computeHash(target.slice(j, j + length));
    if (sourceHashes.has(hashValue)) matches += 1;
  }
  return matches;
}

function levenshteinDistance(a, b) {
  var m = a.length;
  var n = b.length;
  var dp = Array.from({ length: m + 1 }, function() {
    return Array(n + 1).fill(0);
  });
  for (var i = 0; i <= m; i += 1) dp[i][0] = i;
  for (var j = 0; j <= n; j += 1) dp[0][j] = j;
  for (var p = 1; p <= m; p += 1) {
    for (var q = 1; q <= n; q += 1) {
      dp[p][q] = Math.min(
        dp[p - 1][q] + 1,
        dp[p][q - 1] + 1,
        dp[p - 1][q - 1] + (a[p - 1] === b[q - 1] ? 0 : 1)
      );
    }
  }
  return dp[m][n];
}

function cosineSimilarity(wordsA, wordsB) {
  var freqA = buildFrequencyMap(wordsA);
  var freqB = buildFrequencyMap(wordsB);
  var vocabulary = uniqueWords(Object.keys(freqA).concat(Object.keys(freqB)));
  var dot = 0;
  var normA = 0;
  var normB = 0;
  vocabulary.forEach(function(term) {
    var a = freqA[term] || 0;
    var b = freqB[term] || 0;
    dot += a * b;
    normA += a * a;
    normB += b * b;
  });
  return normA === 0 || normB === 0 ? 0 : dot / (Math.sqrt(normA) * Math.sqrt(normB));
}

function binarySearch(sorted, value) {
  var low = 0;
  var high = sorted.length - 1;
  while (low <= high) {
    var mid = Math.floor((low + high) / 2);
    if (sorted[mid] === value) return mid;
    if (sorted[mid] < value) low = mid + 1;
    else high = mid - 1;
  }
  return -1;
}

function computeDivideConquerScore(wordsA, wordsB) {
  var setA = uniqueWords(wordsA).sort();
  var setB = uniqueWords(wordsB).sort();
  if (!setA.length || !setB.length) return 0;
  var matches = setA.reduce(function(count, word) {
    return binarySearch(setB, word) >= 0 ? count + 1 : count;
  }, 0);
  return Math.min(100, Math.round((matches / setA.length) * 100));
}

function computeGreedyScore(wordsA, wordsB) {
  if (!wordsA.length || !wordsB.length) return 0;
  var remaining = wordsB.slice();
  var matchCount = 0;
  wordsA.forEach(function(word) {
    var index = remaining.indexOf(word);
    if (index >= 0) {
      matchCount += 1;
      remaining.splice(index, 1);
    }
  });
  return Math.min(100, Math.round((matchCount / wordsA.length) * 100));
}

function computeBacktrackingScore(wordsA, wordsB) {
  var uniqA = uniqueWords(wordsA);
  var uniqB = uniqueWords(wordsB);
  if (!uniqA.length || !uniqB.length) return 0;
  if (uniqA.length > 14 || uniqB.length > 14) return computeGreedyScore(wordsA, wordsB);
  var best = 0;
  var setB = new Set(uniqB);
  function search(index, count, used) {
    if (index === uniqA.length) {
      best = Math.max(best, count);
      return;
    }
    var remaining = uniqA.length - index;
    if (count + remaining <= best) return;
    var word = uniqA[index];
    if (setB.has(word) && !used[word]) {
      used[word] = true;
      search(index + 1, count + 1, used);
      delete used[word];
    }
    search(index + 1, count, used);
  }
  search(0, 0, {});
  return Math.min(100, Math.round((best / uniqA.length) * 100));
}

function computeBranchAndBoundScore(wordsA, wordsB) {
  var uniqA = uniqueWords(wordsA).sort();
  var uniqB = new Set(uniqueWords(wordsB));
  if (!uniqA.length || !uniqB.size) return 0;
  var best = 0;
  function branch(index, count) {
    if (index === uniqA.length) {
      best = Math.max(best, count);
      return;
    }
    if (count + (uniqA.length - index) <= best) return;
    var word = uniqA[index];
    if (uniqB.has(word)) branch(index + 1, count + 1);
    branch(index + 1, count);
  }
  branch(0, 0);
  return Math.min(100, Math.round((best / uniqA.length) * 100));
}

function computeKMPScore(wordsA, wordsB) {
  if (!wordsA.length || !wordsB.length) return 0;
  var matchCount = 0;
  var target = wordsB.join(' ');
  wordsA.forEach(function(word) {
    if (kmpSearch(target, word) > 0) matchCount += 1;
  });
  return Math.min(100, Math.round((matchCount / wordsA.length) * 100));
}

function computeRabinKarpScore(wordsA, wordsB) {
  if (!wordsA.length || !wordsB.length) return 0;
  var length = Math.min(3, Math.max(1, Math.floor(Math.min(wordsA.length, wordsB.length) / 6)));
  var matches = rollingHashMatches(wordsA, wordsB, length) + rollingHashMatches(wordsB, wordsA, length);
  var maxPossible = Math.max(wordsA.length, wordsB.length);
  return Math.min(100, Math.round((matches / Math.max(maxPossible, 1)) * 100));
}

function computeEditDistanceScore(textA, textB) {
  if (!textA.length || !textB.length) return 0;
  var distance = levenshteinDistance(textA, textB);
  var maxLen = Math.max(textA.length, textB.length);
  return Math.max(0, Math.round((1 - distance / maxLen) * 100));
}

function selectScore(algorithm, dpScore, divideScore, greedyScore, backtrackingScore, branchScore) {
  switch (algorithm) {
    case 'dynamic-programming': return dpScore;
    case 'divide-conquer': return divideScore;
    case 'greedy': return greedyScore;
    case 'backtracking': return backtrackingScore;
    case 'branch-and-bound': return branchScore;
    default: return Math.round((dpScore + divideScore + greedyScore + backtrackingScore + branchScore) / 5);
  }
}

function createVerdict(similarity) {
  if (similarity >= 70) {
    return { class: 'success', title: 'Strong similarity detected', subtitle: 'The selected algorithm indicates a significant overlap between both documents.' };
  }
  if (similarity >= 40) {
    return { class: 'warning', title: 'Moderate similarity observed', subtitle: 'There is notable correspondence in vocabulary and structure that deserves review.' };
  }
  return { class: 'danger', title: 'Low similarity found', subtitle: 'The documents appear distinct, with only minor shared terms or phrasing.' };
}

function safeHtml(value) {
  return String(value).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function highlightText(words, sharedSet) {
  return words.map(function(word) {
    var safe = safeHtml(word);
    if (sharedSet.has(word)) return '<span class="match">' + safe + '</span>';
    return safe;
  }).join(' ');
}

function getNgrams(words, size) {
  if (words.length < size) return [];
  var ngrams = [];
  for (var i = 0; i + size <= words.length; i += 1) {
    ngrams.push(words.slice(i, i + size).join(' '));
  }
  return ngrams;
}

function commonNgrams(wordsA, wordsB, size) {
  var setA = new Set(getNgrams(wordsA, size));
  return getNgrams(wordsB, size).filter(function(gram) {
    return setA.has(gram);
  }).filter(function(value, index, self) {
    return self.indexOf(value) === index;
  });
}

function getSentences(text) {
  return String(text).split(/(?<=[.!?])\s+/).map(function(sentence) {
    return sentence.trim();
  }).filter(Boolean);
}

function sentenceMatchBreakdown(textA, textB) {
  var sentencesA = getSentences(textA);
  var sentencesB = getSentences(textB);
  return sentencesA.map(function(sentenceA) {
    var bestMatch = '';
    var bestScore = 0;
    sentencesB.forEach(function(sentenceB) {
      var score = Math.round(cosineSimilarity(tokenizeWords(sentenceA), tokenizeWords(sentenceB)) * 100);
      if (score > bestScore) {
        bestScore = score;
        bestMatch = sentenceB;
      }
    });
    return { source: sentenceA, match: bestMatch || 'No good candidate found', score: bestScore };
  });
}

function analyzePair(textA, textB, algorithm) {
  var wordsA = tokenizeWords(textA);
  var wordsB = tokenizeWords(textB);
  var setA = new Set(wordsA);
  var setB = new Set(wordsB);
  var sharedTerms = wordsA.filter(function(word) {
    return setB.has(word);
  }).filter(function(value, index, self) {
    return self.indexOf(value) === index;
  });
  var dpScore = computeEditDistanceScore(textA, textB);
  var divideScore = computeDivideConquerScore(wordsA, wordsB);
  var greedyScore = computeGreedyScore(wordsA, wordsB);
  var backtrackingScore = computeBacktrackingScore(wordsA, wordsB);
  var branchScore = computeBranchAndBoundScore(wordsA, wordsB);
  var similarity = selectScore(algorithm, dpScore, divideScore, greedyScore, backtrackingScore, branchScore);
  return {
    counts: { wordsA: wordsA.length, wordsB: wordsB.length, sharedTerms: sharedTerms.length },
    scores: {
      similarity: similarity,
      dynamicProgramming: dpScore,
      divideConquer: divideScore,
      greedy: greedyScore,
      backtracking: backtrackingScore,
      branchAndBound: branchScore
    },
    highlightedA: highlightText(wordsA, new Set(sharedTerms)),
    highlightedB: highlightText(wordsB, new Set(sharedTerms)),
    verdict: createVerdict(similarity),
    sharedTerms: sharedTerms,
    commonPhrases2: commonNgrams(wordsA, wordsB, 2),
    commonPhrases3: commonNgrams(wordsA, wordsB, 3),
    sentenceMatches: sentenceMatchBreakdown(textA, textB),
    algorithm: algorithmData[algorithm] || algorithmData['dynamic-programming']
  };
}

function renderResponse(result) {
  countA.textContent = result.counts.wordsA;
  countB.textContent = result.counts.wordsB;
  metricWordsA.textContent = result.counts.wordsA;
  metricWordsB.textContent = result.counts.wordsB;
  metricShared.textContent = result.counts.sharedTerms;
  metricSimilarity.textContent = result.scores.similarity + '%';
  gaugeValue.textContent = result.scores.similarity + '%';
  if (gaugeFill) {
    gaugeFill.style.background = 'conic-gradient(var(--accent) ' + (result.scores.similarity * 3.6) + 'deg, rgba(148, 163, 184, 0.15) 0deg)';
  }
  if (barDynamicProgramming) barDynamicProgramming.style.width = result.scores.dynamicProgramming + '%';
  if (barDivideConquer) barDivideConquer.style.width = result.scores.divideConquer + '%';
  if (barGreedy) barGreedy.style.width = result.scores.greedy + '%';
  if (barBacktracking) barBacktracking.style.width = result.scores.backtracking + '%';
  if (barBranchAndBound) barBranchAndBound.style.width = result.scores.branchAndBound + '%';
  if (barDynamicProgrammingLabel) barDynamicProgrammingLabel.textContent = result.scores.dynamicProgramming + '%';
  if (barDivideConquerLabel) barDivideConquerLabel.textContent = result.scores.divideConquer + '%';
  if (barGreedyLabel) barGreedyLabel.textContent = result.scores.greedy + '%';
  if (barBacktrackingLabel) barBacktrackingLabel.textContent = result.scores.backtracking + '%';
  if (barBranchAndBoundLabel) barBranchAndBoundLabel.textContent = result.scores.branchAndBound + '%';
  verdictBanner.classList.remove('success', 'warning', 'danger', 'neutral');
  verdictBanner.classList.add(result.verdict.class);
  verdictTitle.textContent = result.verdict.title;
  verdictSubtitle.textContent = result.verdict.subtitle;
  highlightA.innerHTML = result.highlightedA;
  highlightB.innerHTML = result.highlightedB;
  aiReport.textContent = result.report || ('Shared 2-grams: ' + (result.commonPhrases2.slice(0, 8).join(', ') || 'none')); 
  renderNgramSummary(result.commonPhrases2, result.commonPhrases3);
  renderSentenceBreakdown(result.sentenceMatches);
}

function renderNgramSummary(ngrams2, ngrams3) {
  ngramSummary.innerHTML = '<div><strong>2-gram matches:</strong> ' + (ngrams2.slice(0, 8).join(', ') || 'None found') + '</div>' +
    '<div><strong>3-gram matches:</strong> ' + (ngrams3.slice(0, 6).join(', ') || 'None found') + '</div>';
}

function renderSentenceBreakdown(rows) {
  sentenceTable.innerHTML = '';
  if (!rows || !rows.length) {
    sentenceTable.innerHTML = '<tr><td colspan="3">No sentence-level matches available.</td></tr>';
    return;
  }
  rows.slice(0, 7).forEach(function(row) {
    var tr = document.createElement('tr');
    tr.innerHTML = '<td>' + safeHtml(row.source) + '</td>' +
      '<td>' + safeHtml(row.match) + '</td>' +
      '<td>' + row.score + '%</td>';
    sentenceTable.appendChild(tr);
  });
}

function renderMatrix(matrix, labels) {
  matrixTable.innerHTML = '';
  if (!matrix || !matrix.length) {
    matrixTable.textContent = 'Upload or enter multiple documents to see a similarity matrix.';
    return;
  }
  var table = document.createElement('table');
  table.className = 'matrix-table';
  var headerRow = document.createElement('tr');
  headerRow.innerHTML = '<th></th>' + labels.map(function(label) { return '<th>' + safeHtml(label) + '</th>'; }).join('');
  table.appendChild(headerRow);
  matrix.forEach(function(row, rowIndex) {
    var tr = document.createElement('tr');
    tr.innerHTML = '<th>' + safeHtml(labels[rowIndex]) + '</th>' + row.map(function(value) {
      var hue = Math.round(120 - value * 1.2);
      return '<td class="matrix-cell" style="background: hsla(' + hue + ', 80%, 60%, 0.23);">' + value + '%</td>';
    }).join('');
    table.appendChild(tr);
  });
  matrixTable.appendChild(table);
}

function animatePipeline() {
  pipelineSteps.forEach(function(step, index) {
    step.classList.remove('active');
    setTimeout(function() {
      step.classList.add('active');
    }, index * 100);
  });
}

function debounce(fn, wait) {
  var timeout;
  return function() {
    var args = arguments;
    clearTimeout(timeout);
    timeout = setTimeout(function() {
      fn.apply(null, args);
    }, wait);
  };
}

function fetchAnalyze(payload) {
  return fetch('/api/analyze', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(payload)
  }).then(function(response) {
    var contentType = response.headers.get('content-type') || '';
    if (!contentType.includes('application/json')) {
      return response.text().then(function(bodyText) {
        throw new Error('Server returned non-JSON response. Make sure the app is running from the server port and not a stale page. Response begins: ' + bodyText.slice(0, 200));
      });
    }
    if (!response.ok) {
      return response.json().then(function(body) {
        throw new Error(body.error || 'Server analysis failed');
      });
    }
    return response.json();
  });
}

function getActiveTexts() {
  return docs.map(function(doc) {
    return doc.value.trim();
  }).filter(Boolean);
}

function updateCompareButtonState() {
  if (!compareButton) return;
  compareButton.disabled = getActiveTexts().length < 2;
  compareButton.textContent = compareButton.disabled ? 'Add two docs first' : 'Compare now';
}

function updateServerStatus() {
  if (!serverStatus) return;
  if (window.location.protocol === 'file:') {
    serverStatus.textContent = 'Opened from file://. Run npm start and open the app from http://localhost:3005 or the port shown in terminal.';
    serverStatus.classList.add('warning');
  } else {
    serverStatus.textContent = 'Backend endpoint: ' + window.location.origin;
    serverStatus.classList.remove('warning');
  }
}

function calculateMetrics() {
  var texts = getActiveTexts();
  if (texts.length < 2) {
    verdictTitle.textContent = 'Add at least two documents';
    verdictSubtitle.textContent = 'Enter text or upload files to compare multiple documents.';
    updateCompareButtonState();
    return;
  }
  updateCompareButtonState();
  animatePipeline();
  var payload = { texts: texts, algorithm: algorithmSelect.value };
  fetchAnalyze(payload).then(function(response) {
    renderMatrix(response.matrix, response.labels);
    var primary = response.comparisons && response.comparisons[0] && response.comparisons[0].result;
    if (primary) {
      renderResponse(primary);
      saveHistoryEntry({ timestamp: new Date().toISOString(), algorithm: algorithmSelect.value, similarity: primary.scores.similarity, wordsA: primary.counts.wordsA, wordsB: primary.counts.wordsB, docs: response.labels.length });
    }
    if (raceToggle.checked) { startRaceMode(); }
  }).catch(function(error) {
    console.error(error);
    verdictTitle.textContent = 'Comparison failed';
    if (window.location.protocol === 'file:') {
      verdictSubtitle.textContent = 'The page is loaded directly from file:// and cannot reach the backend. Open the app from the local server instead.';
      matrixTable.textContent = 'Please open the app from the server URL shown in the terminal, not via file://.';
    } else {
      verdictSubtitle.textContent = error.message || 'Unable to reach the analysis server.';
      matrixTable.textContent = 'Server unavailable. Start the backend and try again.';
    }
    sentenceTable.innerHTML = '<tr><td colspan="3">No sentence-level analysis because the server is unavailable.</td></tr>';
  });
}

function saveHistoryEntry(entry) {
  var history = JSON.parse(localStorage.getItem('wtDaaHistory') || '[]');
  history.unshift(entry);
  localStorage.setItem('wtDaaHistory', JSON.stringify(history.slice(0, 10)));
  renderHistory();
}

function renderHistory() {
  var history = JSON.parse(localStorage.getItem('wtDaaHistory') || '[]');
  historyList.innerHTML = '';
  if (!history.length) {
    historyList.innerHTML = '<li>No previous comparisons yet.</li>';
    return;
  }
  history.forEach(function(entry) {
    var li = document.createElement('li');
    li.innerHTML = '<strong>' + new Date(entry.timestamp).toLocaleString() + '</strong>' +
      '<div>' + entry.docs + ' docs · ' + entry.algorithm.toUpperCase() + ' · ' + entry.similarity + '%</div>' +
      '<div>' + entry.wordsA + ' / ' + entry.wordsB + ' words</div>';
    historyList.appendChild(li);
  });
}

function clearHistory() {
  localStorage.removeItem('wtDaaHistory');
  renderHistory();
}

function updateTheme() {
  document.body.classList.toggle('light-mode');
  toggleThemeButton.textContent = document.body.classList.contains('light-mode') ? 'Dark mode' : 'Light mode';
}

function fillUploadResults(documents, startingIndex) {
  documents.forEach(function(doc, index) {
    var targetIndex = typeof startingIndex === 'number' ? startingIndex + index : index;
    if (docs[targetIndex]) docs[targetIndex].value = doc.text.trim();
  });
  uploadStatus.textContent = documents.length + ' file' + (documents.length === 1 ? '' : 's') + ' uploaded successfully.';
  updateCompareButtonState();
}

function handleUploadFiles(files, startingIndex) {
  if (!files.length) return;
  var form = new FormData();
  Array.from(files).forEach(function(file) { form.append('files', file); });
  fetch('/api/upload', { method: 'POST', body: form }).then(function(response) {
    if (!response.ok) throw new Error('Upload failed');
    return response.json();
  }).then(function(result) {
    fillUploadResults(result.documents, startingIndex);
    calculateMetrics();
  }).catch(function(error) {
    uploadStatus.textContent = 'Upload failed. Please try PDF, DOCX, or TXT files.';
    console.error('Upload error:', error);
  });
}

function getRaceTiming(wordsCount) {
  var base = Math.max(600, wordsCount * 8);
  return {
    'dynamic-programming': base * 1.45,
    'divide-conquer': base * 0.95,
    greedy: base * 0.9,
    backtracking: base * 1.25,
    'branch-and-bound': base * 1.35
  };
}

function startRaceMode() {
  var texts = getActiveTexts();
  if (texts.length < 2) return;
  var wordsCount = tokenizeWords(texts[0] + ' ' + texts[1]).length;
  var times = getRaceTiming(wordsCount);
  Object.keys(times).forEach(function(key) {
    var fill = document.getElementById('race' + key.replace(/-/g, ''));
    if (fill) {
      fill.style.width = '0%';
      var row = fill.closest('.race-row');
      if (row) row.querySelector('.race-label').textContent = algorithmData[key].label + '...';
    }
  });
  var finishes = [];
  Object.entries(times).forEach(function(entry) {
    var key = entry[0];
    var duration = entry[1];
    setTimeout(function() {
      var fill = document.getElementById('race' + key.replace(/-/g, ''));
      if (fill) {
        fill.style.width = '100%';
        var row = fill.closest('.race-row');
        if (row) row.querySelector('.race-label').textContent = algorithmData[key].label + ' finished';
      }
      finishes.push({ key: key, duration: duration });
      if (finishes.length === 5) {
        finishes.sort(function(a, b) { return a.duration - b.duration; });
        raceStatus.textContent = 'Winner: ' + algorithmData[finishes[0].key].label + ' (simulated fastest).';
      }
    }, duration);
  });
}

function buildDivideConquerSteps(textA, textB) {
  var setA = uniqueWords(tokenizeWords(textA)).sort();
  var setB = uniqueWords(tokenizeWords(textB)).sort();
  var steps = [];
  setA.forEach(function(word) {
    var left = 0;
    var right = setB.length - 1;
    var found = false;
    while (left <= right) {
      var mid = Math.floor((left + right) / 2);
      steps.push({
        note: 'Divide & Conquer binary search for "' + word + '" in sorted words from Document B.',
        sortedB: setB,
        currentWord: word,
        left: left,
        right: right,
        mid: mid,
        testValue: setB[mid],
        found: false
      });
      if (setB[mid] === word) {
        found = true;
        steps.push({
          note: 'Word "' + word + '" found at index ' + mid + '.',
          sortedB: setB,
          currentWord: word,
          left: left,
          right: right,
          mid: mid,
          testValue: setB[mid],
          found: true
        });
        break;
      }
      if (setB[mid] < word) {
        left = mid + 1;
      } else {
        right = mid - 1;
      }
    }
    if (!found) {
      steps.push({
        note: 'Word "' + word + '" not found in Document B.',
        sortedB: setB,
        currentWord: word,
        left: left,
        right: right,
        mid: -1,
        testValue: null,
        found: false
      });
    }
  });
  if (!steps.length) {
    steps.push({ note: 'No unique words available to compare with Divide & Conquer.' });
  }
  return steps;
}

function buildGreedySteps(textA, textB) {
  var a = tokenizeWords(textA);
  var b = tokenizeWords(textB);
  var remaining = b.slice();
  var steps = [{ note: 'Initialize Greedy method: scan words in Document A and match earliest available words in Document B.' }];
  a.forEach(function(word, index) {
    var pos = remaining.indexOf(word);
    if (pos >= 0) {
      steps.push({ note: 'Greedy match: "' + word + '" found in Document B at position ' + pos + '.', word: word, matched: true, index: index, remaining: remaining.slice() });
      remaining.splice(pos, 1);
    } else {
      steps.push({ note: 'Greedy skip: "' + word + '" not found in remaining Document B words.', word: word, matched: false, index: index, remaining: remaining.slice() });
    }
  });
  return steps;
}

function buildBacktrackingSteps(textA, textB) {
  var a = uniqueWords(tokenizeWords(textA));
  var bset = new Set(uniqueWords(tokenizeWords(textB)));
  var steps = [{ note: 'Initialize Backtracking: explore inclusion/exclusion of each unique word from Document A.' }];
  function explore(index, chosen, count) {
    if (index >= a.length) {
      steps.push({ note: 'Backtracking leaf reached with count ' + count + '.', chosen: chosen.slice() });
      return;
    }
    var word = a[index];
    steps.push({ note: 'Consider word "' + word + '" at index ' + index + '.', word: word, index: index, chosen: chosen.slice(), count: count });
    if (bset.has(word)) {
      chosen.push(word);
      steps.push({ note: 'Try including "' + word + '" because it exists in Document B.', word: word, index: index, chosen: chosen.slice(), count: count + 1 });
      explore(index + 1, chosen, count + 1);
      chosen.pop();
      steps.push({ note: 'Backtrack: remove "' + word + '" and try excluding it.', word: word, index: index, chosen: chosen.slice(), count: count });
    }
    explore(index + 1, chosen, count);
  }
  if (a.length > 12) {
    steps.push({ note: 'Backtracking skipped because the unique word set is too large for step-by-step visualization.' });
  } else {
    explore(0, [], 0);
  }
  return steps;
}

function buildBranchAndBoundSteps(textA, textB) {
  var a = uniqueWords(tokenizeWords(textA)).sort();
  var bset = new Set(uniqueWords(tokenizeWords(textB)));
  var steps = [{ note: 'Initialize Branch & Bound search with upper bound pruning.' }];
  var best = 0;
  function search(index, count) {
    var bound = count + (a.length - index);
    steps.push({ note: 'Branch at index ' + index + ' with current count ' + count + ' and bound ' + bound + '.', index: index, count: count, bound: bound, chosen: a.slice(0, index) });
    if (index === a.length) {
      best = Math.max(best, count);
      steps.push({ note: 'Leaf reached. Best count now ' + best + '.', index: index, count: count, best: best });
      return;
    }
    if (bound <= best) {
      steps.push({ note: 'Prune branch at index ' + index + ' because bound ' + bound + ' is not better than best ' + best + '.', index: index, count: count, bound: bound, best: best });
      return;
    }
    var word = a[index];
    if (bset.has(word)) {
      steps.push({ note: 'Branch: include "' + word + '".', word: word, index: index, count: count });
      search(index + 1, count + 1);
    }
    steps.push({ note: 'Branch: exclude "' + word + '".', word: word, index: index, count: count });
    search(index + 1, count);
  }
  if (a.length > 12) {
    steps.push({ note: 'Branch & Bound skipped because the unique word set is too large for step-by-step visualization.' });
  } else {
    search(0, 0);
  }
  return steps;
}

function buildDynamicProgrammingSteps(textA, textB) {
  var a = tokenizeWords(textA);
  var b = tokenizeWords(textB);
  var dp = Array.from({ length: a.length + 1 }, function() { return Array(b.length + 1).fill(0); });
  for (var i = 0; i <= a.length; i += 1) dp[i][0] = i;
  for (var j = 0; j <= b.length; j += 1) dp[0][j] = j;
  var steps = [{ note: 'Initialize DP table.', matrix: dp.map(function(row) { return row.slice(); }) }];
  for (var p = 1; p <= a.length; p += 1) {
    for (var q = 1; q <= b.length; q += 1) {
      dp[p][q] = Math.min(dp[p - 1][q] + 1, dp[p][q - 1] + 1, dp[p - 1][q - 1] + (a[p - 1] === b[q - 1] ? 0 : 1));
      steps.push({ note: 'Filled cell[' + p + '][' + q + '] comparing "' + a[p - 1] + '" with "' + b[q - 1] + '".', matrix: dp.map(function(row) { return row.slice(); }), highlight: { row: p, col: q } });
    }
  }
  return steps;
}

function renderVisualizerStep() {
  var step = visualizerSteps[visualizerIndex] || { note: 'No visualization available.' };
  visualizerDescription.textContent = step.note;
  visualizerOutput.innerHTML = '';
  if (step.matrix) {
    var table = document.createElement('table');
    table.className = 'visualizer-table';
    var headerRow = document.createElement('tr');
    headerRow.innerHTML = '<th></th>' + step.matrix[0].map(function(_, idx) { return '<th>j=' + idx + '</th>'; }).join('');
    table.appendChild(headerRow);
    step.matrix.forEach(function(row, rowIndex) {
      var tr = document.createElement('tr');
      tr.innerHTML = '<th>i=' + rowIndex + '</th>' + row.map(function(cell, colIndex) {
        var classes = step.highlight && step.highlight.row === rowIndex && step.highlight.col === colIndex ? 'highlight' : '';
        return '<td class="' + classes + '">' + cell + '</td>';
      }).join('');
      table.appendChild(tr);
    });
    visualizerOutput.appendChild(table);
  } else if (step.lps) {
    var wrapper = document.createElement('div');
    wrapper.className = 'visualizer-lps';
    step.lps.forEach(function(value, idx) {
      var span = document.createElement('span');
      span.className = 'lps-chip' + (step.highlight && step.highlight.index === idx ? ' active' : '');
      span.textContent = value;
      wrapper.appendChild(span);
    });
    visualizerOutput.appendChild(wrapper);
  } else if (step.sortedB) {
    var info = document.createElement('div');
    info.className = 'visualizer-info';
    info.innerHTML = '<strong>' + safeHtml(step.note) + '</strong>' +
      '<div>Searching for: ' + safeHtml(step.currentWord || '') + '</div>' +
      '<div>Left: ' + step.left + ' right: ' + step.right + ' mid: ' + (step.mid >= 0 ? step.mid : 'N/A') + '</div>' +
      '<div>Test value: ' + safeHtml(step.testValue || 'N/A') + '</div>' +
      '<div>Found: ' + (step.found ? 'yes' : 'no') + '</div>';
    visualizerOutput.appendChild(info);
    var list = document.createElement('div');
    list.className = 'visualizer-list';
    step.sortedB.forEach(function(item, idx) {
      var span = document.createElement('span');
      span.textContent = item;
      if (idx === step.mid) span.className = 'highlight';
      list.appendChild(span);
    });
    visualizerOutput.appendChild(list);
  } else if (step.remaining !== undefined) {
    var block = document.createElement('div');
    block.className = 'visualizer-lines';
    block.innerHTML = '<strong>' + safeHtml(step.note) + '</strong>' +
      '<div>Word: ' + safeHtml(step.word) + '</div>' +
      '<div>Matched: ' + (step.matched ? 'yes' : 'no') + '</div>' +
      '<div>Remaining Document B words: ' + safeHtml(step.remaining.join(', ')) + '</div>';
    visualizerOutput.appendChild(block);
  } else if (step.chosen !== undefined) {
    var block = document.createElement('div');
    block.className = 'visualizer-lines';
    block.innerHTML = '<strong>' + safeHtml(step.note) + '</strong>' +
      (step.word ? '<div>Word: ' + safeHtml(step.word) + '</div>' : '') +
      '<div>Chosen path: ' + safeHtml((step.chosen || []).join(', ')) + '</div>' +
      (step.count !== undefined ? '<div>Count: ' + step.count + '</div>' : '');
    visualizerOutput.appendChild(block);
  } else if (step.lines) {
    var wrapper = document.createElement('div');
    wrapper.className = 'visualizer-lines';
    step.lines.forEach(function(line) {
      var p = document.createElement('p');
      p.textContent = line;
      wrapper.appendChild(p);
    });
    visualizerOutput.appendChild(wrapper);
  } else {
    visualizerOutput.textContent = step.note;
  }
  stepCounter.textContent = (visualizerIndex + 1) + ' / ' + visualizerSteps.length;
}

function activateVisualizer() {
  var texts = getActiveTexts();
  if (texts.length < 2) {
    visualizerDescription.textContent = 'Add two documents first to visualize the algorithm steps.';
    visualizerOutput.textContent = '';
    stepCounter.textContent = '0 / 0';
    return;
  }
  switch (visualizerMode.value) {
    case 'dynamic-programming':
      visualizerSteps = buildDynamicProgrammingSteps(texts[0], texts[1]);
      break;
    case 'divide-conquer':
      visualizerSteps = buildDivideConquerSteps(texts[0], texts[1]);
      break;
    case 'greedy':
      visualizerSteps = buildGreedySteps(texts[0], texts[1]);
      break;
    case 'backtracking':
      visualizerSteps = buildBacktrackingSteps(texts[0], texts[1]);
      break;
    case 'branch-and-bound':
      visualizerSteps = buildBranchAndBoundSteps(texts[0], texts[1]);
      break;
    default:
      visualizerSteps = [{ note: 'Select an algorithm mode to visualize its steps.' }];
  }
  visualizerIndex = 0;
  renderVisualizerStep();
}

function setVisualizerIndex(delta) {
  if (!visualizerSteps.length) return;
  visualizerIndex = Math.max(0, Math.min(visualizerSteps.length - 1, visualizerIndex + delta));
  renderVisualizerStep();
}

function broadcastLive() {
  if (!window.io || !socket || !socket.connected) return;
  socket.emit('liveUpdate', { clientId: socket.id, values: docs.map(function(doc) { return doc.value; }) });
}

var socket;
if (window.io) {
  socket = io();
  socket.on('connect', function() { liveStatus.textContent = 'Live collaboration connected'; });
  socket.on('liveUpdate', function(payload) {
    if (payload.clientId === socket.id) return;
    isRemoteUpdate = true;
    payload.values.forEach(function(value, index) {
      if (docs[index]) docs[index].value = value;
    });
    isRemoteUpdate = false;
    calculateMetrics();
  });
}

var debouncedBroadcast = debounce(broadcastLive, 350);
var debouncedCalculate = debounce(calculateMetrics, 350);

function refreshAlgorithmPanel() {
  var selected = algorithmSelect.value;
  algorithmDescription.textContent = algorithmData[selected].description;
  algorithmComplexity.textContent = algorithmData[selected].complexity;
}

function handleDocUploadChange(event) {
  var input = event.target;
  if (!input.files || !input.files.length) return;
  var docIndex = parseInt(input.dataset.doc, 10);
  handleUploadFiles(input.files, docIndex);
  input.value = '';
}

function updateTheme() {
  document.body.classList.toggle('light-mode');
  toggleThemeButton.textContent = document.body.classList.contains('light-mode') ? 'Dark mode' : 'Light mode';
}

perDocUploadInputs.forEach(function(input) {
  input.addEventListener('change', handleDocUploadChange);
});
algorithmSelect.addEventListener('change', function() { refreshAlgorithmPanel(); calculateMetrics(); });
ngramSelect.addEventListener('change', calculateMetrics);
raceToggle.addEventListener('change', function() { if (raceToggle.checked) startRaceMode(); });
clearHistoryButton.addEventListener('click', clearHistory);
downloadReportButton.addEventListener('click', function() {
  if (window.html2pdf) {
    html2pdf().set({ margin: 0.3, filename: 'wt-daa-report-' + Date.now() + '.pdf' }).from(document.getElementById('reportCard')).save();
  }
});
toggleThemeButton.addEventListener('click', updateTheme);
visualizerMode.addEventListener('change', activateVisualizer);
visualizerPrev.addEventListener('click', function() { setVisualizerIndex(-1); });
visualizerNext.addEventListener('click', function() { setVisualizerIndex(1); });
visualizerReset.addEventListener('click', activateVisualizer);
docs.forEach(function(doc) { doc.addEventListener('input', function() { if (!isRemoteUpdate) { debouncedBroadcast(); updateCompareButtonState(); debouncedCalculate(); } }); });

refreshAlgorithmPanel();
renderHistory();
updateCompareButtonState();
activateVisualizer();
updateServerStatus();
setInterval(function() { document.body.classList.toggle('pulse'); }, 8000);
