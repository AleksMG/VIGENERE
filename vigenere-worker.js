// === KRYPTOS K4 WORKER — OPTIMIZED ===
// Совместим с оригинальным API: init/process → results

let ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
let ALPHABET_SIZE = 26;
let ALPHABET_POSITIONS = {};
let ALPHABET_POS_ARRAY = new Uint8Array(256);
let CIPHERTEXT = "";
let CIPHERTEXT_LENGTH = 0;
let KNOWN_TEXT = "";
let BATCH_SIZE = 100000;
let SCORE_THRESHOLD = 1.0;
let WORKER_ID = 0;
let TEST_SPECIFIC_KEYS = [];

let KNOWN_FRAGMENTS = [];
let KNOWN_REGEX = null;
let ENABLE_K4_MODE = false;
let TRANSPOSITION_WIDTHS = [4, 5, 6, 7, 8];

const ENGLISH_FREQUENCIES = {
    'A': 8.167, 'B': 1.492, 'C': 2.782, 'D': 4.253,
    'E': 12.702, 'F': 2.228, 'G': 2.015, 'H': 6.094,
    'I': 6.966, 'J': 0.153, 'K': 0.772, 'L': 4.025,
    'M': 2.406, 'N': 6.749, 'O': 7.507, 'P': 1.929,
    'Q': 0.095, 'R': 5.987, 'S': 6.327, 'T': 9.056,
    'U': 2.758, 'V': 0.978, 'W': 2.360, 'X': 0.150,
    'Y': 1.974, 'Z': 0.074
};

const COMMON_WORDS = [
    'THE', 'BE', 'TO', 'OF', 'AND', 'A', 'IN', 'THAT', 'HAVE', 'I',
    'IT', 'FOR', 'NOT', 'ON', 'WITH', 'HE', 'AS', 'YOU', 'DO', 'AT',
    'THIS', 'BUT', 'HIS', 'BY', 'FROM', 'THEY', 'WE', 'SAY', 'HER', 'SHE',
    'OR', 'AN', 'WILL', 'MY', 'ONE', 'ALL', 'WOULD', 'THERE', 'THEIR', 'WHAT',
    'SO', 'UP', 'OUT', 'IF', 'ABOUT', 'WHO', 'GET', 'WHICH', 'GO', 'ME',
    'WHEN', 'MAKE', 'CAN', 'LIKE', 'TIME', 'NO', 'JUST', 'HIM', 'KNOW', 'TAKE',
    'PEOPLE', 'INTO', 'YEAR', 'YOUR', 'GOOD', 'SOME', 'COULD', 'THEM', 'SEE', 'OTHER',
    'THAN', 'THEN', 'NOW', 'LOOK', 'ONLY', 'COME', 'ITS', 'OVER', 'THINK', 'ALSO',
    'BACK', 'AFTER', 'USE', 'TWO', 'HOW', 'OUR', 'WORK', 'FIRST', 'WELL', 'WAY',
    'EVEN', 'NEW', 'WANT', 'BECAUSE', 'ANY', 'THESE', 'GIVE', 'DAY', 'MOST', 'US'
];

const COMMON_BIGRAMS = [
    'TH', 'HE', 'IN', 'ER', 'AN', 'RE', 'ND', 'AT', 'ON', 'NT',
    'HA', 'ES', 'ST', 'EN', 'ED', 'TO', 'IT', 'OU', 'EA', 'HI',
    'IS', 'OR', 'TI', 'AS', 'TE', 'ET', 'NG', 'OF', 'AL', 'DE',
    'SE', 'LE', 'SA', 'SI', 'AR', 'VE', 'RA', 'LD', 'UR'
];
const COMMON_TRIGRAMS = [
    'THE', 'AND', 'ING', 'HER', 'HAT', 'HIS', 'THA', 'ERE', 'FOR', 'ENT',
    'ION', 'TER', 'WAS', 'YOU', 'ITH', 'VER', 'ALL', 'WIT', 'THI', 'TIO'
];

// Precomputed word scores + Set для быстрого lookup
const WORD_SCORES = {};
const COMMON_WORDS_SET = new Set(COMMON_WORDS);
const COMMON_BIGRAMS_SET = new Set(COMMON_BIGRAMS);
const COMMON_TRIGRAMS_SET = new Set(COMMON_TRIGRAMS);

COMMON_WORDS.forEach((word, index) => {
    WORD_SCORES[word] = 0.5 + (word.length * 0.3) + (index < 20 ? 0.5 : 0);
});

// === PATTERN ENGINE (расширен для K4) ===
const PatternEngine = (() => {
    const SCAN_LIMIT = 64;
    const vowels = new Set('AEIOU');
    
    return {
        detect(text) {
            const patterns = [];
            if (!text || text.length === 0) return patterns;
            
            const scanText = text.slice(0, SCAN_LIMIT);
            const len = scanText.length;
            
            for (let i = 0; i < len - 3; i++) {
                if (scanText[i] === scanText[i+3] && scanText[i+1] === scanText[i+4]) {
                    patterns.push({ type: 'repeat', seq: scanText.slice(i, i+3), pos: i });
                    break;
                }
            }
            
            for (let i = 0; i < len - 3; i++) {
                if (scanText[i] === scanText[i+3] && scanText[i+1] === scanText[i+2]) {
                    patterns.push({ type: 'palindrome', seq: scanText.slice(i, i+4), pos: i, len: 4 });
                    break;
                }
            }
            
            for (let i = 0; i < len - 4; i++) {
                const sub = scanText.slice(i, i+5);
                if (sub === sub.split('').reverse().join('')) {
                    patterns.push({ type: 'palindrome_long', seq: sub, pos: i, len: 5 });
                    break;
                }
            }
                        let vCount = 0;
            for (let i = 0; i < SCAN_LIMIT && i < text.length; i++) {
                if (vowels.has(text[i])) vCount++;
            }
            const total = Math.min(SCAN_LIMIT, text.length);
            if (total > 0) {
                const vRatio = vCount / total;
                if (vRatio > 0.55) {
                    patterns.push({ type: 'vc_high', ratio: vRatio });
                } else if (vRatio < 0.25) {
                    patterns.push({ type: 'vc_low', ratio: vRatio });
                }
            }
            
            for (let i = 2; i < len; i++) {
                if (scanText[i] === scanText[i-1] && scanText[i] === scanText[i-2]) {
                    patterns.push({ type: 'cluster', char: scanText[i], pos: i });
                    break;
                }
            }
            
            // Known fragments detection with positions
            if (KNOWN_FRAGMENTS.length > 0) {
                const upperText = text.toUpperCase();
                for (const frag of KNOWN_FRAGMENTS) {
                    let pos = 0;
                    while ((pos = upperText.indexOf(frag, pos)) !== -1) {
                        patterns.push({ 
                            type: 'known_fragment', 
                            frag, 
                            pos, 
                            length: frag.length,
                            isFull: true 
                        });
                        pos += frag.length;
                    }
                    // Partial matches (2+ chars)
                    for (let i = 0; i <= frag.length - 2; i++) {
                        const sub = frag.slice(i, i + 2);
                        let subPos = 0;
                        while ((subPos = upperText.indexOf(sub, subPos)) !== -1) {
                            // Не добавляем, если это часть полного совпадения
                            const isPartOfFull = patterns.some(p => 
                                p.type === 'known_fragment' && 
                                p.isFull &&
                                subPos >= p.pos && 
                                subPos < p.pos + p.length
                            );
                            if (!isPartOfFull) {
                                patterns.push({                                     type: 'known_fragment_partial', 
                                    frag: sub, 
                                    pos: subPos, 
                                    length: 2,
                                    isFull: false 
                                });
                            }
                            subPos += 2;
                        }
                    }
                }
            }
            
            return patterns;
        },
        
        getSuggestedTransforms(pattern) {
            const map = {
                'repeat': ['shift_alphabet'],
                'palindrome': ['reverse_segment'],
                'palindrome_long': ['reverse_segment', 'transpose_columns'],
                'vc_high': ['shift_alphabet_neg'],
                'vc_low': ['shift_alphabet_pos'],
                'cluster': ['deshift_alphabet'],
                'known_bad_context': ['partial_reverse'],
                'known_fragment': [], // не трансформировать, это цель
                'known_fragment_partial': []
            };
            return map[pattern.type] || [];
        }
    };
})();

// === TRANSFORMATION ENGINE (оптимизирован) ===
const TransformEngine = (() => {
    return {
        apply(text, key, alphabet, posArray, transformName, pattern) {
            switch (transformName) {
                case 'reverse_segment':
                    return { text: this.reverseSegment(text, pattern.pos, pattern.pos + (pattern.len || 4)), key };
                case 'shift_alphabet':
                case 'shift_alphabet_pos':
                    return { text: this.shiftAlphabet(text, alphabet, posArray, 1), key };
                case 'shift_alphabet_neg':
                    return { text: this.shiftAlphabet(text, alphabet, posArray, -1), key };
                case 'deshift_alphabet':
                    {
                        const shift = pattern.char ? (posArray[pattern.char.charCodeAt(0)] !== 255 ? posArray[pattern.char.charCodeAt(0)] : 1) : 1;
                        return { text: this.shiftAlphabet(text, alphabet, posArray, shift), key };
                    }                case 'partial_reverse':
                    return { text: this.reverseSegment(text, Math.max(0, pattern.pos - 5), pattern.pos + (pattern.frag?.length || 0) + 5), key };
                case 'transpose_columns':
                    return { text: this.transposeColumns(text, pattern.width || 5), key };
                case 'key_mutation_shift':
                    return { text, key: key.slice(1) + key[0] };
                case 'key_mutation_reverse':
                    return { text, key: key.split('').reverse().join('') };
                default:
                    return { text, key };
            }
        },
        
        reverseSegment(text, start, end) {
            if (!text || start >= end || start < 0 || end > text.length) return text;
            const pre = text.slice(0, start);
            const seg = text.slice(start, end).split('').reverse().join('');
            const post = text.slice(end);
            return pre + seg + post;
        },
        
        // ✅ O(n) вместо O(n×alphabet) за счёт posArray
        shiftAlphabet(text, alphabet, posArray, shift) {
            if (!text || !alphabet || alphabet.length === 0) return text;
            const len = alphabet.length;
            const result = new Array(text.length);
            
            for (let i = 0; i < text.length; i++) {
                const code = text.charCodeAt(i);
                const idx = posArray[code];
                if (idx === 255) {
                    result[i] = text[i];
                    continue;
                }
                const newIdx = ((idx + shift) % len + len) % len;
                result[i] = alphabet[newIdx];
            }
            return result.join('');
        },
        
        transposeColumns(text, width) {
            if (!text || text.length === 0) return text;
            const rows = Math.ceil(text.length / width);
            const grid = [];
            for (let r = 0; r < rows; r++) {
                grid.push(text.slice(r * width, (r + 1) * width).padEnd(width, ' '));
            }
            let result = '';
            for (let c = 0; c < width; c++) {
                for (let r = 0; r < rows; r++) {                    result += grid[r][c];
                }
            }
            return result.trim();
        }
    };
})();

function initAlphabetPositions() {
    ALPHABET_POSITIONS = {};
    ALPHABET_POS_ARRAY.fill(255);
    for (let i = 0; i < ALPHABET.length; i++) {
        ALPHABET_POSITIONS[ALPHABET[i]] = i;
        ALPHABET_POS_ARRAY[ALPHABET.charCodeAt(i)] = i;
    }
}

function compileKnownFragments() {
    KNOWN_FRAGMENTS = [];
    KNOWN_REGEX = null;
    if (KNOWN_TEXT && KNOWN_TEXT.trim() !== '') {
        KNOWN_FRAGMENTS = KNOWN_TEXT.split(',').map(f => f.trim().toUpperCase()).filter(f => f.length > 0);
        if (KNOWN_FRAGMENTS.length > 0) {
            const escaped = KNOWN_FRAGMENTS.map(f => f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'));
            KNOWN_REGEX = new RegExp(`(${escaped.join('|')})`, 'gi');
        }
    }
}

// ✅ Vigenère decrypt с O(1) доступом через posArray
function vigenereDecrypt(ciphertext, key, alphabet, posArray) {
    if (!ciphertext || !key || key.length === 0) return "";
    const keyLen = key.length;
    const alphabetSize = alphabet.length;
    const plaintext = new Array(ciphertext.length);
    const keyPositions = new Uint8Array(keyLen);
    
    for (let i = 0; i < keyLen; i++) {
        const pos = posArray[key.charCodeAt(i)];
        if (pos === 255) return "";
        keyPositions[i] = pos;
    }
    
    for (let i = 0; i < ciphertext.length; i++) {
        const cipherPos = posArray[ciphertext.charCodeAt(i)];
        if (cipherPos === 255) {
            plaintext[i] = ciphertext[i]; // сохраняем не-алфавитные символы
            continue;
        }
        let plainPos = (cipherPos - keyPositions[i % keyLen]);        if (plainPos < 0) plainPos += alphabetSize;
        plaintext[i] = alphabet[plainPos % alphabetSize];
    }
    
    return plaintext.join('');
}

// ✅ OPTIMIZED: Один проход по тексту + precomputed Sets
function scoreText(text) {
    if (!text || text.length === 0) return 0;
    
    let score = 0;
    const upperText = text.toUpperCase();
    const textLen = upperText.length;
    
    // Known fragments — высокий приоритет (быстрый lookup)
    if (KNOWN_FRAGMENTS.length > 0) {
        for (const frag of KNOWN_FRAGMENTS) {
            if (frag.length < 2) continue;
            let pos = 0;
            while ((pos = upperText.indexOf(frag, pos)) !== -1) {
                score += 50 * frag.length;
                pos += frag.length;
            }
            // Partial matches (2 chars)
            for (let i = 0; i <= frag.length - 2; i++) {
                const sub = frag.slice(i, i + 2);
                if (upperText.includes(sub)) score += 3;
            }
        }
    }
    
    // Words — через Set для O(1) проверки
    if (textLen >= 3) {
        for (let i = 0; i <= textLen - 3; i++) {
            // Проверяем слова длиной 2-5 для скорости
            for (let wlen = 2; wlen <= 5 && i + wlen <= textLen; wlen++) {
                const word = upperText.slice(i, i + wlen);
                if (COMMON_WORDS_SET.has(word)) {
                    score += WORD_SCORES[word] || 0.5;
                }
            }
        }
    }
    
    // Trigrams — один проход
    if (textLen >= 3) {
        for (let i = 0; i <= textLen - 3; i++) {
            const tri = upperText.slice(i, i + 3);
            if (COMMON_TRIGRAMS_SET.has(tri)) score += 0.5;        }
    }
    
    // Bigrams — один проход
    if (textLen >= 2) {
        for (let i = 0; i <= textLen - 2; i++) {
            const bi = upperText.slice(i, i + 2);
            if (COMMON_BIGRAMS_SET.has(bi)) score += 0.15;
        }
    }
    
    // Frequency analysis — один проход + массив счётчиков
    const charCounts = new Uint16Array(ALPHABET_SIZE);
    let totalChars = 0;
    for (let i = 0; i < textLen; i++) {
        const pos = ALPHABET_POS_ARRAY[upperText.charCodeAt(i)];
        if (pos !== 255) { 
            charCounts[pos]++; 
            totalChars++; 
        }
    }
    
    if (totalChars > 0 && ALPHABET_SIZE > 0) {
        for (let i = 0; i < ALPHABET_SIZE; i++) {
            const char = ALPHABET[i];
            const expected = (ENGLISH_FREQUENCIES[char] || 0) / 100;
            if (expected === 0) continue;
            const observed = charCounts[i] / totalChars;
            const diff = Math.abs(expected - observed);
            score += (1 - diff) * expected * 15;
        }
    }
    
    // Length normalization
    if (textLen > 0) score = score * (Math.min(textLen, 100) / 100);
    return Math.max(0, score);
}

// ✅ K4: detect best transposition width by variance
function detectTranspositionWidth(text, widths) {
    const results = [];
    const upperText = text.toUpperCase();
    
    for (const w of widths) {
        if (w < 2 || w > text.length) continue;
        
        // Group chars by column position
        const colFreqs = Array.from({length: w}, () => new Uint16Array(ALPHABET_SIZE));
        for (let i = 0; i < upperText.length; i++) {
            const pos = ALPHABET_POS_ARRAY[upperText.charCodeAt(i)];            if (pos !== 255) {
                colFreqs[i % w][pos]++;
            }
        }
        
        // Score each column independently
        const colScores = colFreqs.map(freqs => {
            const total = freqs.reduce((a,b) => a+b, 0);
            if (total < 3) return 0;
            let s = 0;
            for (let i = 0; i < ALPHABET_SIZE; i++) {
                if (freqs[i] === 0) continue;
                const expected = (ENGLISH_FREQUENCIES[ALPHABET[i]] || 0) / 100;
                const observed = freqs[i] / total;
                s += (1 - Math.abs(expected - observed)) * expected;
            }
            return s * 10;
        });
        
        // High variance between columns = likely transposition
        const avg = colScores.reduce((a,b) => a+b, 0) / colScores.length;
        const variance = colScores.reduce((sum, v) => sum + Math.pow(v - avg, 2), 0) / colScores.length;
        
        if (variance > 2.0 && avg > 0.5) {
            results.push({ width: w, score: avg, variance });
        }
    }
    
    return results.sort((a,b) => b.score - a.score)[0]?.width || null;
}

// ✅ Generate attack variants with dynamic transposition
function getAttackVariants(ciphertext, key) {
    const variants = [];
    variants.push({ text: ciphertext, attack: 'original', key, description: 'Standard Vigenère' });
    variants.push({ text: ciphertext.split('').reverse().join(''), attack: 'reverse_ct', key, description: 'Reversed ciphertext' });
    variants.push({ text: ciphertext, attack: 'key_reverse', key: key.split('').reverse().join(''), description: 'Reversed key' });
    
    if (ALPHABET_SIZE === 26) {
        variants.push({ text: ciphertext, attack: 'alphabet_shift+1', key, customAlphabet: ALPHABET.slice(1) + ALPHABET[0], description: 'Alphabet shifted +1' });
        variants.push({ text: ciphertext, attack: 'alphabet_shift-1', key, customAlphabet: ALPHABET[ALPHABET.length - 1] + ALPHABET.slice(0, -1), description: 'Alphabet shifted -1' });
    }
    
    // Dynamic transposition widths
    if (ENABLE_K4_MODE && CIPHERTEXT_LENGTH > 20) {
        const bestWidth = detectTranspositionWidth(ciphertext, TRANSPOSITION_WIDTHS);
        if (bestWidth) {
            variants.push({ 
                text: TransformEngine.transposeColumns(ciphertext, bestWidth), 
                attack: `transpose_${bestWidth}`,                 key, 
                description: `Columnar transposition (${bestWidth})`,
                autoDetected: true 
            });
        }
    } else {
        // Fallback to configured widths
        for (const w of TRANSPOSITION_WIDTHS.slice(0, 3)) {
            variants.push({ 
                text: TransformEngine.transposeColumns(ciphertext, w), 
                attack: `transpose_${w}`, 
                key, 
                description: `Columnar transposition (${w})` 
            });
        }
    }
    
    return variants;
}

// ✅ Extract match positions for UI highlighting
function extractFragmentMatches(text) {
    const matches = [];
    if (!KNOWN_FRAGMENTS.length) return matches;
    
    const upperText = text.toUpperCase();
    for (const frag of KNOWN_FRAGMENTS) {
        let pos = 0;
        while ((pos = upperText.indexOf(frag, pos)) !== -1) {
            matches.push({
                start: pos,
                end: pos + frag.length,
                text: frag,
                type: 'full'
            });
            pos += frag.length;
        }
        // Partial (2-char) matches
        for (let i = 0; i <= frag.length - 2; i++) {
            const sub = frag.slice(i, i + 2);
            let subPos = 0;
            while ((subPos = upperText.indexOf(sub, subPos)) !== -1) {
                // Skip if part of full match
                const isPartOfFull = matches.some(m => 
                    m.type === 'full' && subPos >= m.start && subPos < m.end
                );
                if (!isPartOfFull) {
                    matches.push({
                        start: subPos,
                        end: subPos + 2,                        text: sub,
                        type: 'partial'
                    });
                }
                subPos += 2;
            }
        }
    }
    return matches.sort((a,b) => a.start - b.start);
}

// ✅ Early termination: estimate max possible score
function estimateMaxScore(textLen, knownFragments) {
    if (textLen === 0) return 0;
    let max = 0;
    // Max from known fragments (all could match)
    for (const frag of knownFragments) {
        max += 50 * frag.length + (frag.length - 1) * 3;
    }
    // Max from trigrams/bigrams (theoretical)
    max += Math.floor(textLen / 3) * 0.5 + Math.floor(textLen / 2) * 0.15;
    // Max from frequency (perfect match)
    max += ALPHABET_SIZE * 0.15;
    return max * Math.min(textLen, 100) / 100;
}

function processBatch(ciphertext, keys) {
    const results = [];
    const startTime = performance.now();
    const threshold = SCORE_THRESHOLD * 0.5;
    const MAX_TRANSFORMS_PER_KEY = 2;
    
    // Specific keys testing
    if (TEST_SPECIFIC_KEYS.length > 0 && keys.length === 0) {
        for (const testKey of TEST_SPECIFIC_KEYS) {
            const variants = getAttackVariants(ciphertext, testKey);
            for (const variant of variants) {
                let decryptAlphabet = ALPHABET;
                let decryptPosArray = ALPHABET_POS_ARRAY;
                
                if (variant.customAlphabet) {
                    decryptAlphabet = variant.customAlphabet;
                    decryptPosArray = new Uint8Array(256);
                    decryptPosArray.fill(255);
                    for (let i = 0; i < decryptAlphabet.length; i++) {
                        decryptPosArray[decryptAlphabet.charCodeAt(i)] = i;
                    }
                }
                
                const plaintext = vigenereDecrypt(variant.text, variant.key, decryptAlphabet, decryptPosArray);                if (!plaintext) continue;
                
                // Early pruning
                const maxPossible = estimateMaxScore(plaintext.length, KNOWN_FRAGMENTS);
                if (maxPossible < threshold) continue;
                
                let baseScore = scoreText(plaintext);
                let bestResult = { 
                    plaintext, 
                    key: testKey, 
                    score: baseScore, 
                    transforms: [], 
                    patterns: [], 
                    attack: variant.attack, 
                    baseScore: baseScore,
                    fragmentMatches: extractFragmentMatches(plaintext)
                };
                
                const patterns = PatternEngine.detect(plaintext);
                if (patterns.length > 0 && ENABLE_AUTO_TRANSFORM) {
                    let currentText = plaintext;
                    let currentKey = testKey;
                    let currentScore = baseScore;
                    let appliedTransforms = [];
                    let detectedPatterns = [];
                    
                    for (const pattern of patterns) {
                        if (appliedTransforms.length >= MAX_TRANSFORMS_PER_KEY) break;
                        const suggested = PatternEngine.getSuggestedTransforms(pattern);
                        for (const transformName of suggested) {
                            const result = TransformEngine.apply(
                                currentText, currentKey, decryptAlphabet, decryptPosArray, transformName, pattern
                            );
                            const transformedText = result.text;
                            const transformedKey = result.key || currentKey;
                            if (!transformedText || transformedText === currentText) continue;
                            
                            const newScore = scoreText(transformedText);
                            const improvement = newScore - currentScore;
                            if (improvement > 0.5) {
                                currentText = transformedText;
                                currentKey = transformedKey;
                                currentScore = newScore;
                                appliedTransforms.push(transformName.split('_').pop() + '[' + pattern.type + ']');
                                detectedPatterns.push(pattern.type);
                                
                                if (currentScore > bestResult.score) {
                                    bestResult = { 
                                        plaintext: currentText, 
                                        key: currentKey,                                         score: currentScore, 
                                        transforms: [...appliedTransforms], 
                                        patterns: [...detectedPatterns], 
                                        attack: variant.attack, 
                                        baseScore: baseScore,
                                        fragmentMatches: extractFragmentMatches(currentText)
                                    };
                                }
                            }
                        }
                    }
                }
                
                if (bestResult.score > threshold) {
                    results.push({
                        key: bestResult.key,
                        plaintext: bestResult.plaintext,
                        score: parseFloat(bestResult.score.toFixed(2)),
                        baseScore: parseFloat(bestResult.baseScore.toFixed(2)),
                        transforms: bestResult.transforms,
                        patterns: bestResult.patterns,
                        attack: bestResult.attack,
                        attackDescription: variant.description,
                        isSpecificKey: true,
                        fragmentMatches: bestResult.fragmentMatches,
                        autoDetected: variant.autoDetected || false
                    });
                }
            }
        }
    }
    
    // Regular batch processing
    for (const key of keys) {
        try {
            const plaintext = vigenereDecrypt(ciphertext, key, ALPHABET, ALPHABET_POS_ARRAY);
            if (!plaintext) continue;
            
            const maxPossible = estimateMaxScore(plaintext.length, KNOWN_FRAGMENTS);
            if (maxPossible < threshold) continue;
            
            let baseScore = scoreText(plaintext);
            let bestResult = { 
                plaintext, 
                key, 
                score: baseScore, 
                transforms: [], 
                patterns: [], 
                attack: 'bruteforce', 
                baseScore: baseScore,                fragmentMatches: extractFragmentMatches(plaintext)
            };
            
            const patterns = PatternEngine.detect(plaintext);
            if (patterns.length > 0 && ENABLE_AUTO_TRANSFORM) {
                let currentText = plaintext;
                let currentKey = key;
                let currentScore = baseScore;
                let appliedTransforms = [];
                let detectedPatterns = [];
                
                for (const pattern of patterns) {
                    if (appliedTransforms.length >= MAX_TRANSFORMS_PER_KEY) break;
                    const suggested = PatternEngine.getSuggestedTransforms(pattern);
                    for (const transformName of suggested) {
                        const result = TransformEngine.apply(
                            currentText, currentKey, ALPHABET, ALPHABET_POS_ARRAY, transformName, pattern
                        );
                        const transformedText = result.text;
                        const transformedKey = result.key || currentKey;
                        if (!transformedText || transformedText === currentText) continue;
                        
                        const newScore = scoreText(transformedText);
                        const improvement = newScore - currentScore;
                        if (improvement > 0.5) {
                            currentText = transformedText;
                            currentKey = transformedKey;
                            currentScore = newScore;
                            appliedTransforms.push(transformName.split('_').pop() + '[' + pattern.type + ']');
                            detectedPatterns.push(pattern.type);
                            
                            if (currentScore > bestResult.score) {
                                bestResult = { 
                                    plaintext: currentText, 
                                    key: currentKey, 
                                    score: currentScore, 
                                    transforms: [...appliedTransforms], 
                                    patterns: [...detectedPatterns], 
                                    attack: 'bruteforce', 
                                    baseScore: baseScore,
                                    fragmentMatches: extractFragmentMatches(currentText)
                                };
                            }
                        }
                    }
                }
            }
            
            if (bestResult.score > threshold) {
                results.push({                    key: bestResult.key,
                    plaintext: bestResult.plaintext,
                    score: parseFloat(bestResult.score.toFixed(2)),
                    baseScore: parseFloat(bestResult.baseScore.toFixed(2)),
                    transforms: bestResult.transforms,
                    patterns: bestResult.patterns,
                    attack: bestResult.attack,
                    attackDescription: 'Brute force',
                    isSpecificKey: false,
                    fragmentMatches: bestResult.fragmentMatches,
                    autoDetected: false
                });
            }
        } catch (e) {
            console.error('Error processing key:', key, e);
            continue;
        }
    }
    
    const batchTime = performance.now() - startTime;
    return {
        keysTested: keys.length,
        results: results,
        currentSpeed: batchTime > 0 ? Math.round((keys.length / batchTime) * 1000) : 0
    };
}

onmessage = function(e) {
    if (e.data.type === 'init') {
        ALPHABET = e.data.alphabet || "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        ALPHABET_SIZE = ALPHABET.length;
        CIPHERTEXT = e.data.ciphertext || "";
        CIPHERTEXT_LENGTH = e.data.ciphertextLength || 0;
        KNOWN_TEXT = e.data.knownText || "";
        BATCH_SIZE = e.data.batchSize || 100000;
        SCORE_THRESHOLD = e.data.scoreThreshold || 1.0;
        WORKER_ID = e.data.workerId || 0;
        TEST_SPECIFIC_KEYS = e.data.testSpecificKeys || [];
        ENABLE_K4_MODE = e.data.enableK4Mode || false;
        TRANSPOSITION_WIDTHS = e.data.transpositionWidths || [4, 5, 6, 7, 8];
        
        initAlphabetPositions();
        compileKnownFragments();
        return;
    }

    if (e.data.type === 'process') {
        const result = processBatch(e.data.ciphertext, e.data.keys);
        postMessage({
            keysTested: result.keysTested,            results: result.results,
            currentSpeed: result.currentSpeed,
            workerId: WORKER_ID
        });
    }
    
    if (e.data.type === 'stop') {
        // Soft stop flag for long operations
        // (можно расширить для прерывания внутри processBatch)
        return;
    }
};
