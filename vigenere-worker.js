// Worker state
let ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
let ALPHABET_SIZE = 26;
let ALPHABET_MAP = {};
let CIPHERTEXT = "";
let CT_POS = null;
let KNOWN_FRAGMENTS = [];
let KNOWN_REGEX = null;
let BATCH_SIZE = 100000;
let SCORE_THRESHOLD = 1.0;
let WORKER_ID = 0;
let TEST_KEYS = [];

// === PRECOMPUTED TABLES ===
let DECRYPT_TABLE = null;
let BIGRAM_TABLE = null;
let TRIGRAM_TABLE = null;
let WORD_SCORES = null;

// === PRECOMPUTED ATTACK VARIANTS ===
let ATTACK_CT_VARIANTS = [];

// === INIT ALL TABLES (called once at startup) ===
function initTables() {
    // 1. Alphabet map for O(1) lookup
    ALPHABET_MAP = {};
    for (let i = 0; i < ALPHABET_SIZE; i++) {
        ALPHABET_MAP[ALPHABET[i]] = i;
    }
    
    // 2. Decrypt table: DECRYPT_TABLE[cipherIndex][keyIndex] = plainIndex
    DECRYPT_TABLE = new Array(ALPHABET_SIZE);
    for (let c = 0; c < ALPHABET_SIZE; c++) {
        DECRYPT_TABLE[c] = new Int8Array(ALPHABET_SIZE);
        for (let k = 0; k < ALPHABET_SIZE; k++) {
            let p = c - k;
            if (p < 0) p += ALPHABET_SIZE;
            DECRYPT_TABLE[c][k] = p;
        }
    }
    
    // 3. Bigram table (26*26 = 676 entries) - PRECOMPUTED
    BIGRAM_TABLE = new Float32Array(676);
    const bigrams = {
        'TH': 3.0, 'HE': 3.0, 'IN': 3.0, 'ER': 3.0, 'AN': 3.0,
        'RE': 3.0, 'ND': 3.0, 'AT': 3.0, 'ON': 3.0, 'NT': 3.0,
        'HA': 2.0, 'ES': 2.0, 'ST': 2.0, 'EN': 2.0, 'ED': 2.0,
        'TO': 2.0, 'IT': 2.0, 'OU': 2.0, 'EA': 2.0, 'HI': 2.0,
        'IS': 2.0, 'OR': 2.0, 'TI': 2.0, 'AS': 2.0, 'TE': 2.0,
        'ET': 2.0, 'NG': 2.0, 'OF': 2.0, 'AL': 2.0, 'DE': 2.0,        'SE': 2.0, 'LE': 2.0, 'SA': 2.0, 'SI': 2.0, 'AR': 2.0,
        'VE': 2.0, 'RA': 2.0, 'LD': 2.0, 'UR': 2.0
    };
    for (let i = 0; i < 676; i++) {
        BIGRAM_TABLE[i] = 0.1;
    }
    for (const bg in bigrams) {
        if (ALPHABET_MAP[bg[0]] !== undefined && ALPHABET_MAP[bg[1]] !== undefined) {
            const idx = ALPHABET_MAP[bg[0]] * 26 + ALPHABET_MAP[bg[1]];
            BIGRAM_TABLE[idx] = bigrams[bg];
        }
    }
    
    // 4. Trigram table (26*26*26 = 17576 entries) - PRECOMPUTED
    TRIGRAM_TABLE = new Float32Array(17576);
    const trigrams = {
        'THE': 6.0, 'AND': 6.0, 'ING': 6.0, 'HER': 5.0, 'HIS': 5.0,
        'THA': 5.0, 'ERE': 5.0, 'FOR': 5.0, 'ENT': 5.0, 'ION': 5.0,
        'TER': 4.0, 'WAS': 4.0, 'YOU': 4.0, 'ITH': 4.0, 'VER': 4.0,
        'ALL': 4.0, 'WIT': 4.0, 'THI': 4.0, 'TIO': 4.0, 'HAT': 4.0,
        'HES': 4.0, 'NCE': 4.0, 'TIO': 4.0, 'NTE': 4.0, 'ERS': 4.0,
        'STA': 4.0, 'TED': 4.0, 'STE': 4.0, 'STR': 4.0, 'CON': 4.0,
        'COM': 4.0, 'DIS': 4.0, 'TIN': 4.0, 'PAR': 4.0, 'EAS': 4.0,
        'AST': 4.0, 'RTH': 4.0, 'ORT': 4.0, 'NOR': 4.0, 'OCK': 4.0,
        'CLO': 4.0, 'LIN': 4.0, 'BER': 4.0
    };
    for (let i = 0; i < 17576; i++) {
        TRIGRAM_TABLE[i] = 0.2;
    }
    for (const tg in trigrams) {
        if (ALPHABET_MAP[tg[0]] !== undefined && ALPHABET_MAP[tg[1]] !== undefined && ALPHABET_MAP[tg[2]] !== undefined) {
            const idx = ALPHABET_MAP[tg[0]] * 676 + ALPHABET_MAP[tg[1]] * 26 + ALPHABET_MAP[tg[2]];
            TRIGRAM_TABLE[idx] = trigrams[tg];
        }
    }
    
    // 5. Word scores - PRECOMPUTED
    WORD_SCORES = {};
    const words = [
        'THE', 'BE', 'TO', 'OF', 'AND', 'A', 'IN', 'THAT', 'HAVE', 'I',
        'IT', 'FOR', 'NOT', 'ON', 'WITH', 'HE', 'AS', 'YOU', 'DO', 'AT',
        'THIS', 'BUT', 'HIS', 'BY', 'FROM', 'THEY', 'WE', 'SAY', 'HER', 'SHE',
        'OR', 'AN', 'WILL', 'MY', 'ONE', 'ALL', 'WOULD', 'THERE', 'THEIR', 'WHAT',
        'SO', 'UP', 'OUT', 'IF', 'ABOUT', 'WHO', 'GET', 'WHICH', 'GO', 'ME',
        'WHEN', 'MAKE', 'CAN', 'LIKE', 'TIME', 'NO', 'JUST', 'HIM', 'KNOW', 'TAKE',
        'PEOPLE', 'INTO', 'YEAR', 'YOUR', 'GOOD', 'SOME', 'COULD', 'THEM', 'SEE', 'OTHER',
        'THAN', 'THEN', 'NOW', 'LOOK', 'ONLY', 'COME', 'ITS', 'OVER', 'THINK', 'ALSO',
        'BACK', 'AFTER', 'USE', 'TWO', 'HOW', 'OUR', 'WORK', 'FIRST', 'WELL', 'WAY',
        'EVEN', 'NEW', 'WANT', 'BECAUSE', 'ANY', 'THESE', 'GIVE', 'DAY', 'MOST', 'US',
        'BERLIN', 'EAST', 'NORTH', 'CLOCK', 'KRYPTOS', 'PALIMPSEST', 'ABSCISSA'    ];
    for (let i = 0; i < words.length; i++) {
        const w = words[i];
        WORD_SCORES[w] = 1.0 + w.length * 0.5 + (i < 20 ? 3.0 : 0);
    }
}

// === PRECOMPUTE CIPHERTEXT POSITIONS ===
function precomputeCT(ct) {
    const len = ct.length;
    const pos = new Int8Array(len);
    for (let i = 0; i < len; i++) {
        const p = ALPHABET_MAP[ct[i]];
        if (p === undefined) return null;
        pos[i] = p;
    }
    return pos;
}

// === PRECOMPUTE ATTACK VARIANTS (all run in parallel for each key) ===
function initAttackVariants(ctPos) {
    ATTACK_CT_VARIANTS = [];
    
    // 1. Original ciphertext
    ATTACK_CT_VARIANTS.push({
        name: 'original',
        ctPos: ctPos,
        description: 'Standard Vigenère'
    });
    
    // 2. Reversed ciphertext (before decrypt)
    const revCt = new Int8Array(ctPos.length);
    for (let i = 0; i < ctPos.length; i++) {
        revCt[i] = ctPos[ctPos.length - 1 - i];
    }
    ATTACK_CT_VARIANTS.push({
        name: 'reverse_ct',
        ctPos: revCt,
        description: 'Reversed ciphertext'
    });
    
    // 3. Columnar transposition width=5
    ATTACK_CT_VARIANTS.push({
        name: 'transpose_5',
        ctPos: transposePos(ctPos, 5),
        description: 'Columnar transposition (5)'
    });
    
    // 4. Columnar transposition width=7
    ATTACK_CT_VARIANTS.push({        name: 'transpose_7',
        ctPos: transposePos(ctPos, 7),
        description: 'Columnar transposition (7)'
    });
    
    // 5. Columnar transposition width=10
    if (ctPos.length >= 10) {
        ATTACK_CT_VARIANTS.push({
            name: 'transpose_10',
            ctPos: transposePos(ctPos, 10),
            description: 'Columnar transposition (10)'
        });
    }
}

// === COLUMNAR TRANSPOSITION ===
function transposePos(pos, width) {
    const len = pos.length;
    const rows = Math.ceil(len / width);
    const result = new Int8Array(len);
    let idx = 0;
    for (let c = 0; c < width; c++) {
        for (let r = 0; r < rows; r++) {
            const p = r * width + c;
            if (p < len) {
                result[idx] = pos[p];
                idx++;
            }
        }
    }
    return result;
}

// === PRECOMPUTE KEY POSITIONS ===
function precomputeKey(key) {
    const klen = key.length;
    const kpos = new Int8Array(klen);
    for (let i = 0; i < klen; i++) {
        const p = ALPHABET_MAP[key[i]];
        if (p === undefined) return null;
        kpos[i] = p;
    }
    return kpos;
}

// === ULTRA-FAST DECRYPT (uses precomputed DECRYPT_TABLE) ===
function decryptFast(ctPos, keyPos, klen) {
    const len = ctPos.length;
    const result = new Int8Array(len);
    for (let i = 0; i < len; i++) {        result[i] = DECRYPT_TABLE[ctPos[i]][keyPos[i % klen]];
    }
    return result;
}

// === FAST SCORE (uses BIGRAM_TABLE + TRIGRAM_TABLE lookups) ===
function scoreFast(plainPos, len) {
    if (len < 3) return 0;
    
    let score = 0;
    
    // Bigrams lookup (FAST - no string operations)
    for (let i = 0; i < len - 1; i++) {
        const idx = plainPos[i] * 26 + plainPos[i + 1];
        score += BIGRAM_TABLE[idx];
    }
    
    // Trigrams lookup (FAST - no string operations)
    for (let i = 0; i < len - 2; i++) {
        const idx = plainPos[i] * 676 + plainPos[i + 1] * 26 + plainPos[i + 2];
        score += TRIGRAM_TABLE[idx];
    }
    
    // Normalize by length
    return score * Math.min(1.0, len / 100);
}

// === CHECK KNOWN FRAGMENTS (only for good candidates) ===
function checkKnown(plainPos, len) {
    if (!KNOWN_REGEX || len < 3) return 0;
    
    // Convert to string only when needed
    let text = '';
    const checkLen = Math.min(200, len);
    for (let i = 0; i < checkLen; i++) {
        text += ALPHABET[plainPos[i]];
    }
    
    const matches = text.match(KNOWN_REGEX);
    if (matches) {
        let bonus = 0;
        for (let m = 0; m < matches.length; m++) {
            bonus += 10 + matches[m].length * 2;
        }
        return bonus;
    }
    return 0;
}

// === CHECK COMMON WORDS (only for good candidates) ===function checkWords(plainPos, len) {
    if (len < 3) return 0;
    
    let text = '';
    const checkLen = Math.min(200, len);
    for (let i = 0; i < checkLen; i++) {
        text += ALPHABET[plainPos[i]];
    }
    
    let bonus = 0;
    for (const word in WORD_SCORES) {
        if (text.indexOf(word) >= 0) {
            bonus += WORD_SCORES[word];
        }
    }
    return bonus;
}

// === CONVERT POS TO STRING (only for results) ===
function posToString(pos) {
    let result = '';
    for (let i = 0; i < pos.length; i++) {
        result += ALPHABET[pos[i]];
    }
    return result;
}

// === TEXT TRANSFORMS (improve readability with SAME KEY) ===
function reverseSegmentPos(pos, start, end) {
    const result = pos.slice();
    for (let i = start, j = end - 1; i < j; i++, j--) {
        const tmp = result[i];
        result[i] = result[j];
        result[j] = tmp;
    }
    return result;
}

function shiftPos(pos, shift) {
    const result = new Int8Array(pos.length);
    for (let i = 0; i < pos.length; i++) {
        let v = pos[i] + shift;
        if (v < 0) v += ALPHABET_SIZE;
        result[i] = v % ALPHABET_SIZE;
    }
    return result;
}

// === PATTERN DETECT (finds issues in decrypted text) ===
function detectPatternsPos(pos, len) {    const patterns = [];
    const scan = Math.min(64, len);
    
    // Detect repeating sequences
    for (let i = 0; i < scan - 3; i++) {
        if (pos[i] === pos[i+3] && pos[i+1] === pos[i+4]) {
            patterns.push({ type: 'repeat', pos: i });
            break;
        }
    }
    
    // Detect palindromes
    for (let i = 0; i < scan - 3; i++) {
        if (pos[i] === pos[i+3] && pos[i+1] === pos[i+2]) {
            patterns.push({ type: 'palindrome', pos: i, len: 4 });
            break;
        }
    }
    
    // Detect vowel/consonant anomaly
    const vowels = { 'A':1, 'E':1, 'I':1, 'O':1, 'U':1 };
    let vCount = 0;
    for (let i = 0; i < scan; i++) {
        if (vowels[ALPHABET[pos[i]]]) vCount++;
    }
    const vRatio = vCount / scan;
    if (vRatio > 0.55) {
        patterns.push({ type: 'vc_high', ratio: vRatio });
    } else if (vRatio < 0.25) {
        patterns.push({ type: 'vc_low', ratio: vRatio });
    }
    
    // Detect known fragment with bad context
    if (KNOWN_FRAGMENTS.length > 0) {
        for (let f = 0; f < KNOWN_FRAGMENTS.length; f++) {
            const frag = KNOWN_FRAGMENTS[f];
            const fragLen = frag.length;
            if (len < fragLen) continue;
            
            // Search for fragment
            for (let i = 0; i <= len - fragLen; i++) {
                let match = true;
                for (let j = 0; j < fragLen; j++) {
                    if (ALPHABET[pos[i + j]] !== frag[j]) {
                        match = false;
                        break;
                    }
                }
                if (match) {
                    // Check context                    const ctxStart = Math.max(0, i - 5);
                    const ctxEnd = Math.min(len, i + fragLen + 5);
                    let noise = 0;
                    let ctxLen = 0;
                    for (let k = ctxStart; k < ctxEnd; k++) {
                        if (k >= i && k < i + fragLen) continue;
                        ctxLen++;
                        const ch = ALPHABET[pos[k]];
                        if (!vowels[ch] && 'BCDFGHJKLMNPQRSTVWXYZ'.indexOf(ch) >= 0) {
                            noise++;
                        }
                    }
                    if (ctxLen > 0 && noise / ctxLen > 0.6) {
                        patterns.push({ type: 'known_bad_context', frag: frag, pos: i });
                    }
                    break;
                }
            }
        }
    }
    
    return patterns;
}

// === APPLY TRANSFORMS TO IMPROVE TEXT (same key, better readability) ===
function applyTransforms(plainPos, len, baseScore) {
    const threshold = SCORE_THRESHOLD * 0.5;
    
    if (baseScore < threshold) {
        return { pos: plainPos, score: baseScore, transforms: [], patterns: [] };
    }
    
    let bestPos = plainPos;
    let bestScore = baseScore;
    let transforms = [];
    let patterns = [];
    
    const detected = detectPatternsPos(plainPos, len);
    if (detected.length === 0) {
        return { pos: plainPos, score: baseScore, transforms: [], patterns: [] };
    }
    
    let current = plainPos;
    let currentScore = baseScore;
    
    for (let p = 0; p < detected.length; p++) {
        if (transforms.length >= 2) break;
        
        const pattern = detected[p];
                if (pattern.type === 'palindrome') {
            const transformed = reverseSegmentPos(current, pattern.pos, pattern.pos + 4);
            const newScore = scoreFast(transformed, transformed.length) + checkKnown(transformed, transformed.length) + checkWords(transformed, transformed.length);
            if (newScore > currentScore + 1.0) {
                current = transformed;
                currentScore = newScore;
                transforms.push('REV[PAL]');
                patterns.push('palindrome');
                if (currentScore > bestScore) {
                    bestPos = current;
                    bestScore = currentScore;
                }
            }
        } else if (pattern.type === 'repeat') {
            const transformed = shiftPos(current, 1);
            const newScore = scoreFast(transformed, transformed.length) + checkKnown(transformed, transformed.length) + checkWords(transformed, transformed.length);
            if (newScore > currentScore + 1.0) {
                current = transformed;
                currentScore = newScore;
                transforms.push('SHIFT[RPT]');
                patterns.push('repeat');
                if (currentScore > bestScore) {
                    bestPos = current;
                    bestScore = currentScore;
                }
            }
        } else if (pattern.type === 'vc_high' || pattern.type === 'vc_low') {
            const transformed = shiftPos(current, pattern.type === 'vc_high' ? -1 : 1);
            const newScore = scoreFast(transformed, transformed.length) + checkKnown(transformed, transformed.length) + checkWords(transformed, transformed.length);
            if (newScore > currentScore + 1.0) {
                current = transformed;
                currentScore = newScore;
                transforms.push('SHIFT[VC]');
                patterns.push(pattern.type);
                if (currentScore > bestScore) {
                    bestPos = current;
                    bestScore = currentScore;
                }
            }
        } else if (pattern.type === 'known_bad_context') {
            const transformed = reverseSegmentPos(current, Math.max(0, pattern.pos - 5), Math.min(len, pattern.pos + pattern.frag.length + 5));
            const newScore = scoreFast(transformed, transformed.length) + checkKnown(transformed, transformed.length) + checkWords(transformed, transformed.length);
            if (newScore > currentScore + 1.0) {
                current = transformed;
                currentScore = newScore;
                transforms.push('REV[CTX]');
                patterns.push('known_bad_context');
                if (currentScore > bestScore) {
                    bestPos = current;
                    bestScore = currentScore;                }
            }
        }
    }
    
    return { pos: bestPos, score: bestScore, transforms: transforms, patterns: patterns };
}

// === PROCESS BATCH (main loop - ALL features active) ===
function processBatch(ciphertext, keys) {
    const results = [];
    const startTime = performance.now();
    const threshold = SCORE_THRESHOLD * 0.5;
    
    const ctPos = CT_POS;
    if (!ctPos) {
        return { keysTested: keys.length, results: [], currentSpeed: 0 };
    }
    
    for (let k = 0; k < keys.length; k++) {
        const key = keys[k];
        const keyPos = precomputeKey(key);
        if (!keyPos) continue;
        const klen = keyPos.length;
        
        // === ALL ATTACK VARIANTS RUN IN PARALLEL FOR EACH KEY ===
        for (let v = 0; v < ATTACK_CT_VARIANTS.length; v++) {
            const variant = ATTACK_CT_VARIANTS[v];
            
            // Decrypt using this variant's ciphertext
            const plainPos = decryptFast(variant.ctPos, keyPos, klen);
            
            // Fast score using PRECOMPUTED bigram/trigram tables
            let baseScore = scoreFast(plainPos, plainPos.length);
            
            // Add known fragment bonus
            const knownBonus = checkKnown(plainPos, plainPos.length);
            baseScore += knownBonus;
            
            // Add word bonus
            const wordBonus = checkWords(plainPos, plainPos.length);
            baseScore += wordBonus;
            
            if (baseScore < threshold) continue;
            
            // Apply transforms to improve readability (SAME KEY, better text)
            const transformed = applyTransforms(plainPos, plainPos.length, baseScore);
            
            if (transformed.score > threshold) {
                results.push({                    key: key,
                    plaintext: posToString(transformed.pos),
                    score: parseFloat(transformed.score.toFixed(2)),
                    baseScore: parseFloat(baseScore.toFixed(2)),
                    transforms: transformed.transforms,
                    patterns: transformed.patterns,
                    attack: variant.name,
                    attackDescription: variant.description,
                    isSpecificKey: TEST_KEYS.length > 0 && keys.length === 0
                });
            }
        }
    }
    
    const elapsed = performance.now() - startTime;
    return {
        keysTested: keys.length,
        results: results,
        currentSpeed: elapsed > 0 ? Math.round((keys.length / elapsed) * 1000) : 0
    };
}

// === MESSAGE HANDLER ===
onmessage = function(e) {
    if (e.data.type === 'init') {
        ALPHABET = e.data.alphabet || "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        ALPHABET_SIZE = ALPHABET.length;
        CIPHERTEXT = e.data.ciphertext || "";
        BATCH_SIZE = e.data.batchSize || 100000;
        SCORE_THRESHOLD = e.data.scoreThreshold || 1.0;
        WORKER_ID = e.data.workerId || 0;
        TEST_KEYS = e.data.testSpecificKeys || [];
        
        const knownFrags = (e.data.knownText || "").split(',').map(function(f) { return f.trim().toUpperCase(); }).filter(function(f) { return f.length > 0; });
        KNOWN_FRAGMENTS = knownFrags;
        
        if (knownFrags.length > 0) {
            const escaped = knownFrags.map(function(f) {
                return f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
            });
            KNOWN_REGEX = new RegExp('(' + escaped.join('|') + ')', 'gi');
        }
        
        // Initialize ALL tables and variants
        initTables();
        CT_POS = precomputeCT(CIPHERTEXT);
        if (CT_POS) {
            initAttackVariants(CT_POS);
        }
                return;
    }

    if (e.data.type === 'process') {
        const result = processBatch(e.data.ciphertext, e.data.keys);
        postMessage({
            keysTested: result.keysTested,
            results: result.results,
            currentSpeed: result.currentSpeed,
            workerId: WORKER_ID
        });
    }
};
