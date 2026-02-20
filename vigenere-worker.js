// Worker state
let ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
let ALPHABET_SIZE = 26;
let ALPHABET_POSITIONS = {};
let ALPHABET_POS_ARRAY = new Uint8Array(256);
let CIPHERTEXT_LENGTH = 0;
let KNOWN_TEXT = "";
let BATCH_SIZE = 100000;
let SCORE_THRESHOLD = 1.0;
let WORKER_ID = 0;

// === OPTIMIZATION: Precompiled known fragments ===
let KNOWN_FRAGMENTS = [];
let KNOWN_REGEX = null;

// Frequency data
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
// Precompute word scores
const WORD_SCORES = {};
COMMON_WORDS.forEach((word, index) => {
    WORD_SCORES[word] = 0.5 + (word.length * 0.3) + (index < 20 ? 0.5 : 0);
});

// === ADAPTIVE PATTERN ENGINE ===
const PatternEngine = (() => {
    const SCAN_LIMIT = 64;
    const vowels = new Set('AEIOU');
    
    return {
        detect(text) {
            const patterns = [];
            if (!text || text.length === 0) return patterns;
            
            const scanText = text.slice(0, SCAN_LIMIT);
            const len = scanText.length;
            
            // 1. Повторяющиеся последовательности
            for (let i = 0; i < len - 3; i++) {
                if (scanText[i] === scanText[i+3] && scanText[i+1] === scanText[i+4]) {
                    patterns.push({ type: 'repeat', seq: scanText.slice(i, i+3), pos: i });
                    break;
                }
            }
            
            // 2. Палиндромы (4 символа)
            for (let i = 0; i < len - 3; i++) {
                if (scanText[i] === scanText[i+3] && scanText[i+1] === scanText[i+2]) {
                    patterns.push({ type: 'palindrome', seq: scanText.slice(i, i+4), pos: i, len: 4 });
                    break;
                }
            }
            
            // 3. Длинные палиндромы (5+)
            for (let i = 0; i < len - 4; i++) {
                const sub = scanText.slice(i, i+5);
                if (sub === sub.split('').reverse().join('')) {
                    patterns.push({ type: 'palindrome_long', seq: sub, pos: i, len: 5 });
                    break;
                }
            }
            
            // 4. Аномалия гласных/согласных
            let vCount = 0;
            for (let i = 0; i < SCAN_LIMIT && i < text.length; i++) {
                if (vowels.has(text[i])) vCount++;
            }            const total = Math.min(SCAN_LIMIT, text.length);
            if (total > 0) {
                const vRatio = vCount / total;
                if (vRatio > 0.55) {
                    patterns.push({ type: 'vc_high', ratio: vRatio });
                } else if (vRatio < 0.25) {
                    patterns.push({ type: 'vc_low', ratio: vRatio });
                }
            }
            
            // 5. Кластеры одинаковых букв
            for (let i = 2; i < len; i++) {
                if (scanText[i] === scanText[i-1] && scanText[i] === scanText[i-2]) {
                    patterns.push({ type: 'cluster', char: scanText[i], pos: i });
                    break;
                }
            }
            
            // 6. Known-fragment с плохим окружением
            if (KNOWN_REGEX && KNOWN_FRAGMENTS.length > 0) {
                for (const frag of KNOWN_FRAGMENTS) {
                    const idx = text.toUpperCase().indexOf(frag);
                    if (idx !== -1) {
                        const before = text.slice(Math.max(0, idx - 5), idx);
                        const after = text.slice(idx + frag.length, idx + frag.length + 5);
                        const context = before + after;
                        if (context.length > 0) {
                            let noise = 0;
                            for (const c of context) {
                                if (ALPHABET_POS_ARRAY[c.charCodeAt(0)] === 255) noise++;
                            }
                            if (noise / context.length > 0.3) {
                                patterns.push({ type: 'known_bad_context', frag, pos: idx });
                            }
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
                'cluster': ['deshift_alphabet'],                'known_bad_context': ['partial_reverse']
            };
            return map[pattern.type] || [];
        }
    };
})();

// === TRANSFORMATION ENGINE ===
const TransformEngine = (() => {
    return {
        apply(text, key, alphabet, transformName, pattern) {
            switch (transformName) {
                case 'reverse_segment':
                    return { text: this.reverseSegment(text, pattern.pos, pattern.pos + (pattern.len || 4)), key };
                
                case 'shift_alphabet':
                case 'shift_alphabet_pos':
                    return { text: this.shiftAlphabet(text, alphabet, 1), key };
                
                case 'shift_alphabet_neg':
                    return { text: this.shiftAlphabet(text, alphabet, -1), key };
                
                case 'deshift_alphabet':
                    return { text: this.shiftAlphabet(text, alphabet, pattern.char ? alphabet.indexOf(pattern.char) : 1), key };
                
                case 'partial_reverse':
                    return { text: this.reverseSegment(text, Math.max(0, pattern.pos - 5), pattern.pos + (pattern.frag?.length || 0) + 5), key };
                
                case 'transpose_columns':
                    return { text: this.transposeColumns(text, 5), key };
                
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
                shiftAlphabet(text, alphabet, shift) {
            if (!text || !alphabet || alphabet.length === 0) return text;
            const len = alphabet.length;
            return text.split('').map(c => {
                const idx = alphabet.indexOf(c);
                if (idx < 0) return c;
                const newIdx = ((idx + shift) % len + len) % len;
                return alphabet[newIdx];
            }).join('');
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
                for (let r = 0; r < rows; r++) {
                    result += grid[r][c];
                }
            }
            return result.trim();
        }
    };
})();

// Initialize alphabet positions
function initAlphabetPositions() {
    ALPHABET_POSITIONS = {};
    ALPHABET_POS_ARRAY.fill(255);
    for (let i = 0; i < ALPHABET.length; i++) {
        ALPHABET_POSITIONS[ALPHABET[i]] = i;
        ALPHABET_POS_ARRAY[ALPHABET.charCodeAt(i)] = i;
    }
}

// Precompile known fragments
function compileKnownFragments() {
    KNOWN_FRAGMENTS = [];
    KNOWN_REGEX = null;
    if (KNOWN_TEXT && KNOWN_TEXT.trim() !== '') {
        KNOWN_FRAGMENTS = KNOWN_TEXT.split(',').map(f => f.trim().toUpperCase()).filter(f => f.length > 0);
        if (KNOWN_FRAGMENTS.length > 0) {
            const escaped = KNOWN_FRAGMENTS.map(f => f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'));
            KNOWN_REGEX = new RegExp(`(${escaped.join('|')})`, 'gi');
        }
    }}

// Optimized Vigenère decryption
function vigenereDecrypt(ciphertext, key) {
    if (!ciphertext || !key || key.length === 0) return "";
    
    const keyLen = key.length;
    const plaintext = new Array(ciphertext.length);
    const keyPositions = new Uint8Array(keyLen);
    
    for (let i = 0; i < keyLen; i++) {
        const pos = ALPHABET_POS_ARRAY[key.charCodeAt(i)];
        if (pos === 255) return "";
        keyPositions[i] = pos;
    }
    
    for (let i = 0; i < ciphertext.length; i++) {
        const cipherPos = ALPHABET_POS_ARRAY[ciphertext.charCodeAt(i)];
        if (cipherPos === 255) return "";
        
        let plainPos = (cipherPos - keyPositions[i % keyLen]) % ALPHABET_SIZE;
        if (plainPos < 0) plainPos += ALPHABET_SIZE;
        
        plaintext[i] = ALPHABET[plainPos];
    }
    
    return plaintext.join('');
}

// Scoring algorithm
function scoreText(text) {
    if (!text || text.length === 0) return 0;
    
    let score = 0;
    const upperText = text.toUpperCase();
    const textLen = upperText.length;
    
    // Common words
    if (textLen >= 3) {
        for (const word in WORD_SCORES) {
            if (word.length > textLen) continue;
            let pos = 0;
            while ((pos = upperText.indexOf(word, pos)) !== -1) {
                score += WORD_SCORES[word];
                pos += word.length;
            }
        }
    }
    
    // Known fragments    if (KNOWN_REGEX) {
        const matches = upperText.match(KNOWN_REGEX);
        if (matches) {
            for (const m of matches) {
                score += 5 + (m.length * 1.5);
            }
        }
    }
    
    // Trigrams
    if (textLen >= 3) {
        for (const trigram of COMMON_TRIGRAMS) {
            let pos = 0;
            while ((pos = upperText.indexOf(trigram, pos)) !== -1) {
                score += 0.3;
                pos += trigram.length;
            }
        }
    }
    
    // Bigrams
    if (textLen >= 2) {
        for (const bigram of COMMON_BIGRAMS) {
            let pos = 0;
            while ((pos = upperText.indexOf(bigram, pos)) !== -1) {
                score += 0.1;
                pos += bigram.length;
            }
        }
    }
    
    // Frequency analysis
    const charCounts = new Uint16Array(26);
    let totalChars = 0;
    
    for (let i = 0; i < textLen; i++) {
        const pos = ALPHABET_POS_ARRAY[upperText.charCodeAt(i)];
        if (pos !== 255) {
            charCounts[pos]++;
            totalChars++;
        }
    }
    
    if (totalChars > 0) {
        const freqKeys = Object.keys(ENGLISH_FREQUENCIES);
        for (let i = 0; i < freqKeys.length; i++) {
            const char = freqKeys[i];
            const pos = ALPHABET_POSITIONS[char];
            if (pos !== undefined) {
                const expected = ENGLISH_FREQUENCIES[char] / 100;                const observed = charCounts[pos] / totalChars;
                const diff = Math.abs(expected - observed);
                score += (1 - diff) * expected * 15;
            }
        }
    }
    
    // Normalize
    if (textLen > 0) {
        score = score * (Math.min(textLen, 100) / 100);
    }
    
    return Math.max(0, score);
}

// === ADAPTIVE PROCESS BATCH ===
function processBatch(ciphertext, keys) {
    const results = [];
    const startTime = performance.now();
    const threshold = SCORE_THRESHOLD * 0.5;
    const MAX_TRANSFORMS_PER_KEY = 2;
    
    for (const key of keys) {
        try {
            // 1. Базовый decrypt
            const plaintext = vigenereDecrypt(ciphertext, key);
            if (!plaintext) continue;
            
            // 2. Базовый скор
            let baseScore = scoreText(plaintext);
            let bestResult = {
                plaintext,
                key,
                score: baseScore,
                transforms: [],
                patterns: []
            };
            
            // 3. Детекция паттернов
            const patterns = PatternEngine.detect(plaintext);
            
            // 4. Адаптивные трансформации
            if (patterns.length > 0) {
                let currentText = plaintext;
                let currentKey = key;
                let currentScore = baseScore;
                let appliedTransforms = [];
                let detectedPatterns = [];
                
                for (const pattern of patterns) {                    if (appliedTransforms.length >= MAX_TRANSFORMS_PER_KEY) break;
                    
                    const suggested = PatternEngine.getSuggestedTransforms(pattern);
                    
                    for (const transformName of suggested) {
                        const result = TransformEngine.apply(currentText, currentKey, ALPHABET, transformName, pattern);
                        const transformedText = result.text;
                        const transformedKey = result.key || currentKey;
                        
                        if (!transformedText || transformedText === currentText) continue;
                        
                        const newScore = scoreText(transformedText);
                        const improvement = newScore - currentScore;
                        
                        if (improvement > 0.5) {
                            currentText = transformedText;
                            currentKey = transformedKey;
                            currentScore = newScore;
                            appliedTransforms.push(`${transformName.split('_').pop()}[${pattern.type}]`);
                            detectedPatterns.push(pattern.type);
                            
                            if (currentScore > bestResult.score) {
                                bestResult = {
                                    plaintext: currentText,
                                    key: currentKey,
                                    score: currentScore,
                                    transforms: [...appliedTransforms],
                                    patterns: [...detectedPatterns],
                                    baseScore
                                };
                            }
                        }
                    }
                }
            }
            
            // 5. Push если порог пройден
            if (bestResult.score > threshold) {
                results.push({
                    key: bestResult.key,
                    plaintext: bestResult.plaintext,
                    score: parseFloat(bestResult.score.toFixed(2)),
                    baseScore: parseFloat((bestResult.baseScore || bestResult.score).toFixed(2)),
                    transforms: bestResult.transforms,
                    patterns: bestResult.patterns
                });
            }
        } catch (e) {
            console.error('Error processing key:', key, e);
            continue;        }
    }
    
    const batchTime = performance.now() - startTime;
    const currentSpeed = batchTime > 0 ? Math.round((keys.length / batchTime) * 1000) : 0;
    
    return {
        keysTested: keys.length,
        results,
        currentSpeed
    };
}

// Main message handler
onmessage = function(e) {
    if (e.data.type === 'init') {
        ALPHABET = e.data.alphabet || "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        ALPHABET_SIZE = ALPHABET.length;
        CIPHERTEXT_LENGTH = e.data.ciphertextLength || 0;
        KNOWN_TEXT = e.data.knownText || "";
        BATCH_SIZE = e.data.batchSize || 100000;
        SCORE_THRESHOLD = e.data.scoreThreshold || 1.0;
        WORKER_ID = e.data.workerId || 0;
        
        initAlphabetPositions();
        compileKnownFragments();
        return;
    }

    if (e.data.type === 'process') {
        const result = processBatch(e.data.ciphertext, e.data.keys);
        postMessage({
            ...result,
            workerId: WORKER_ID
        });
    }
};
