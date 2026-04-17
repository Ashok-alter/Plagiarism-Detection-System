const express = require('express');
const path = require('path');
const multer = require('multer');
const pdfParse = require('pdf-parse');
const mammoth = require('mammoth');
const app = express();
const port = process.env.PORT || 3000;

const upload = multer({ storage: multer.memoryStorage() });

app.use(express.json());
app.use(express.static(path.join(__dirname)));

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
  return words.reduce((map, word) => {
    map[word] = (map[word] || 0) + 1;
    return map;
  }, {});
}

function kmpSearch(text, pattern) {
  const n = text.length;
  const m = pattern.length;
  if (m === 0) return 0;
  const lps = Array(m).fill(0);
  let len = 0;
  for (let i = 1; i < m; ) {
    if (pattern[i] === pattern[len]) {
      len += 1;
      lps[i++] = len;
    } else if (len !== 0) {
      len = lps[len - 1];
    } else {
      lps[i++] = 0;
    }
  }
  let i = 0;
  let j = 0;
  let count = 0;
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
  const base = 257;
  const mod = 1000000007;
  function computeHash(arr) {
    return arr.reduce((hash, token) => {
      for (let i = 0; i < token.length; i += 1) {
        hash = (hash * base + token.charCodeAt(i)) % mod;
      }
      return hash;
    }, 0);
  }
  const sourceHashes = new Set();
  for (let i = 0; i + length <= source.length; i += 1) {
    sourceHashes.add(computeHash(source.slice(i, i + length)));
  }
  let matches = 0;
  for (let j = 0; j + length <= target.length; j += 1) {
    const hashValue = computeHash(target.slice(j, j + length));
    if (sourceHashes.has(hashValue)) matches += 1;
  }
  return matches;
}

function levenshteinDistance(a, b) {
  const m = a.length;
  const n = b.length;
  const dp = Array.from({ length: m + 1 }, () => Array(n + 1).fill(0));
  for (let i = 0; i <= m; i += 1) dp[i][0] = i;
  for (let j = 0; j <= n; j += 1) dp[0][j] = j;
  for (let i = 1; i <= m; i += 1) {
    for (let j = 1; j <= n; j += 1) {
      dp[i][j] = Math.min(
        dp[i - 1][j] + 1,
        dp[i][j - 1] + 1,
        dp[i - 1][j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1)
      );
    }
  }
  return dp[m][n];
}

function cosineSimilarity(wordsA, wordsB) {
  const freqA = buildFrequencyMap(wordsA);
  const freqB = buildFrequencyMap(wordsB);
  const vocabulary = uniqueWords([...Object.keys(freqA), ...Object.keys(freqB)]);
  let dot = 0;
  let normA = 0;
  let normB = 0;
  vocabulary.forEach(term => {
    const a = freqA[term] || 0;
    const b = freqB[term] || 0;
    dot += a * b;
    normA += a * a;
    normB += b * b;
  });
  return normA === 0 || normB === 0 ? 0 : dot / (Math.sqrt(normA) * Math.sqrt(normB));
}

function binarySearch(sorted, value) {
  let low = 0;
  let high = sorted.length - 1;
  while (low <= high) {
    const mid = Math.floor((low + high) / 2);
    if (sorted[mid] === value) return mid;
    if (sorted[mid] < value) low = mid + 1;
    else high = mid - 1;
  }
  return -1;
}

function computeDivideConquerScore(wordsA, wordsB) {
  const setA = uniqueWords(wordsA).sort();
  const setB = uniqueWords(wordsB).sort();
  if (!setA.length || !setB.length) return 0;
  const matches = setA.reduce((count, word) => (binarySearch(setB, word) >= 0 ? count + 1 : count), 0);
  return Math.min(100, Math.round((matches / setA.length) * 100));
}

function computeGreedyScore(wordsA, wordsB) {
  if (!wordsA.length || !wordsB.length) return 0;
  const remaining = wordsB.slice();
  let matchCount = 0;
  wordsA.forEach(word => {
    const index = remaining.indexOf(word);
    if (index >= 0) {
      matchCount += 1;
      remaining.splice(index, 1);
    }
  });
  return Math.min(100, Math.round((matchCount / wordsA.length) * 100));
}

function computeBacktrackingScore(wordsA, wordsB) {
  const uniqA = uniqueWords(wordsA);
  const uniqB = uniqueWords(wordsB);
  if (!uniqA.length || !uniqB.length) return 0;
  if (uniqA.length > 14 || uniqB.length > 14) return computeGreedyScore(wordsA, wordsB);
  let best = 0;
  const setB = new Set(uniqB);
  function search(index, count, used) {
    if (index === uniqA.length) {
      best = Math.max(best, count);
      return;
    }
    if (count + (uniqA.length - index) <= best) return;
    const word = uniqA[index];
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
  const uniqA = uniqueWords(wordsA).sort();
  const uniqB = new Set(uniqueWords(wordsB));
  if (!uniqA.length || !uniqB.size) return 0;
  let best = 0;
  function branch(index, count) {
    if (index === uniqA.length) {
      best = Math.max(best, count);
      return;
    }
    if (count + (uniqA.length - index) <= best) return;
    const word = uniqA[index];
    if (uniqB.has(word)) branch(index + 1, count + 1);
    branch(index + 1, count);
  }
  branch(0, 0);
  return Math.min(100, Math.round((best / uniqA.length) * 100));
}

function computeKMPScore(wordsA, wordsB) {
  if (!wordsA.length || !wordsB.length) return 0;
  let matchCount = 0;
  const target = wordsB.join(' ');
  wordsA.forEach(word => {
    const count = kmpSearch(target, word);
    if (count > 0) matchCount += 1;
  });
  return Math.min(100, Math.round((matchCount / wordsA.length) * 100));
}

function computeRabinKarpScore(wordsA, wordsB) {
  if (!wordsA.length || !wordsB.length) return 0;
  const length = Math.min(3, Math.max(1, Math.floor(Math.min(wordsA.length, wordsB.length) / 6)));
  const matches = rollingHashMatches(wordsA, wordsB, length) + rollingHashMatches(wordsB, wordsA, length);
  const maxPossible = Math.max(wordsA.length, wordsB.length);
  return Math.min(100, Math.round((matches / Math.max(maxPossible, 1)) * 100));
}

function computeEditDistanceScore(textA, textB) {
  if (!textA.length || !textB.length) return 0;
  const distance = levenshteinDistance(textA, textB);
  const maxLen = Math.max(textA.length, textB.length);
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
    return {
      class: 'success',
      title: 'Strong similarity detected',
      subtitle: 'The selected algorithm indicates a significant overlap between both documents.'
    };
  }
  if (similarity >= 40) {
    return {
      class: 'warning',
      title: 'Moderate similarity observed',
      subtitle: 'There is notable correspondence in vocabulary and structure that deserves review.'
    };
  }
  return {
    class: 'danger',
    title: 'Low similarity found',
    subtitle: 'The documents appear distinct, with only minor shared terms or phrasing.'
  };
}

function safeHtml(value) {
  return String(value)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}

function highlightText(words, sharedSet) {
  return words.map(word => {
    const safe = safeHtml(word);
    return sharedSet.has(word)
      ? `<span class="match">${safe}</span>`
      : safe;
  }).join(' ');
}

function getNgrams(words, size) {
  if (words.length < size) return [];
  const ngrams = [];
  for (let i = 0; i + size <= words.length; i += 1) {
    ngrams.push(words.slice(i, i + size).join(' '));
  }
  return ngrams;
}

function commonNgrams(wordsA, wordsB, size) {
  const setA = new Set(getNgrams(wordsA, size));
  return getNgrams(wordsB, size).filter((gram, index, self) => setA.has(gram) && self.indexOf(gram) === index);
}

function getSentences(text) {
  return String(text).split(/(?<=[.!?])\s+/).map(sentence => sentence.trim()).filter(Boolean);
}

function sentenceMatchBreakdown(textA, textB) {
  const sentencesA = getSentences(textA);
  const sentencesB = getSentences(textB);
  return sentencesA.map(sentenceA => {
    let bestMatch = '';
    let bestScore = 0;
    sentencesB.forEach(sentenceB => {
      const score = Math.round(cosineSimilarity(tokenizeWords(sentenceA), tokenizeWords(sentenceB)) * 100);
      if (score > bestScore) {
        bestScore = score;
        bestMatch = sentenceB;
      }
    });
    return { source: sentenceA, match: bestMatch || 'No good candidate found', score: bestScore };
  });
}

const allowedTypes = new Set([
  'application/pdf',
  'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
  'text/plain'
]);

async function parseDocument(file) {
  const mimetype = file.mimetype || '';
  if (mimetype === 'application/pdf' || file.originalname.match(/\.pdf$/i)) {
    const data = await pdfParse(file.buffer);
    return data.text || '';
  }
  if (mimetype === 'application/vnd.openxmlformats-officedocument.wordprocessingml.document' || file.originalname.match(/\.docx$/i)) {
    const result = await mammoth.extractRawText({ buffer: file.buffer });
    return result.value || '';
  }
  if (mimetype === 'text/plain' || file.originalname.match(/\.txt$/i)) {
    return file.buffer.toString('utf8');
  }
  throw new Error('Unsupported file type: ' + file.originalname);
}

function computeSimilarity(textA, textB, algorithm) {
  if (textA === textB) return 100;
  const wordsA = tokenizeWords(textA);
  const wordsB = tokenizeWords(textB);
  const dpScore = computeEditDistanceScore(textA, textB);
  const divideScore = computeDivideConquerScore(wordsA, wordsB);
  const greedyScore = computeGreedyScore(wordsA, wordsB);
  const backtrackingScore = computeBacktrackingScore(wordsA, wordsB);
  const branchScore = computeBranchAndBoundScore(wordsA, wordsB);
  return selectScore(algorithm, dpScore, divideScore, greedyScore, backtrackingScore, branchScore);
}

function analyzePair(textA, textB, algorithm) {
  const wordsA = tokenizeWords(textA);
  const wordsB = tokenizeWords(textB);
  const setA = new Set(wordsA);
  const setB = new Set(wordsB);
  const sharedTerms = [...setA].filter(word => setB.has(word));
  const dpScore = computeEditDistanceScore(textA, textB);
  const divideScore = computeDivideConquerScore(wordsA, wordsB);
  const greedyScore = computeGreedyScore(wordsA, wordsB);
  const backtrackingScore = computeBacktrackingScore(wordsA, wordsB);
  const branchScore = computeBranchAndBoundScore(wordsA, wordsB);
  const similarity = selectScore(algorithm, dpScore, divideScore, greedyScore, backtrackingScore, branchScore);
  const verdict = createVerdict(similarity);
  const highlightedA = highlightText(wordsA, new Set(sharedTerms));
  const highlightedB = highlightText(wordsB, new Set(sharedTerms));
  const sentenceMatches = sentenceMatchBreakdown(textA, textB);
  return {
    counts: { wordsA: wordsA.length, wordsB: wordsB.length, sharedTerms: sharedTerms.length },
    scores: {
      similarity,
      dynamicProgramming: dpScore,
      divideConquer: divideScore,
      greedy: greedyScore,
      backtracking: backtrackingScore,
      branchAndBound: branchScore
    },
    highlightedA,
    highlightedB,
    verdict,
    sharedTerms,
    commonPhrases2: commonNgrams(wordsA, wordsB, 2),
    commonPhrases3: commonNgrams(wordsA, wordsB, 3),
    sentenceMatches,
    algorithm: algorithmData[algorithm] || algorithmData['dynamic-programming']
  };
}

function analyzeDocuments(texts, algorithm) {
  const labels = texts.map((_, idx) => `Doc ${idx + 1}`);
  const matrix = texts.map((source, i) => texts.map((target, j) => (i === j ? 100 : computeSimilarity(source, target, algorithm))));
  const comparisons = [];
  for (let i = 0; i < texts.length; i += 1) {
    for (let j = i + 1; j < texts.length; j += 1) {
      comparisons.push({
        docA: i,
        docB: j,
        result: analyzePair(texts[i], texts[j], algorithm)
      });
    }
  }
  return { labels, matrix, comparisons };
}

app.post('/api/upload', upload.array('files'), async (req, res) => {
  try {
    if (!req.files || !req.files.length) {
      return res.status(400).json({ error: 'No files uploaded' });
    }
    const documents = await Promise.all(req.files.map(async file => ({
      name: file.originalname,
      text: (await parseDocument(file)).trim()
    })));
    res.json({ documents });
  } catch (error) {
    console.error('Upload parse error:', error);
    res.status(400).json({ error: 'Unable to parse uploaded files. Use PDF, DOCX, or TXT.' });
  }
});

app.post('/api/analyze', (req, res) => {
  const { texts = [], algorithm = 'dynamic-programming' } = req.body;
  if (!Array.isArray(texts) || texts.length < 2) {
    return res.status(400).json({ error: 'Provide at least two documents for analysis.' });
  }
  const analysis = analyzeDocuments(texts, algorithm);
  res.json(analysis);
});

function startServer(listenPort) {
  app.listen(listenPort, () => {
    console.log(`WT-DAA backend is running at http://localhost:${listenPort}`);
  }).on('error', (error) => {
    if (error.code === 'EADDRINUSE') {
      console.warn(`Port ${listenPort} is in use. Trying port ${listenPort + 1}...`);
      startServer(listenPort + 1);
    } else {
      console.error('Server failed to start:', error);
      process.exit(1);
    }
  });
}

startServer(port);
