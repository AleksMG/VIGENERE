// Worker state
let ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
let ALPHABET_SIZE = 26;
let ALPHABET_MAP = {};
let CIPHERTEXT = "";
let CT_LENGTH = 0;
let KNOWN_REGEX = null;
let BATCH_SIZE = 100000;
let SCORE_THRESHOLD = 1.0;
let WORKER_ID = 0;
let TEST_KEYS = [];

// === PRECOMPUTED TABLES (init once) ===
let DECRYPT_TABLE = null; // [26][26] = plaintext char index
let BIGRAM_TABLE = null;  // [26][26] = score
let TRIGRAM_TABLE = null; // [26][26][26] = score

// === INIT TABLES (вызывается 1 раз при старте) ===
function initTables() {
    // Alphabet lookup
    ALPHABET_MAP = {};
    for (let i = 0; i < ALPHABET_SIZE; i++) {
        ALPHABET_MAP[ALPHABET[i]] = i;
    }
    
    // Decryption table: DECRYPT_TABLE[cipherPos][keyPos] = plainPos
    DECRYPT_TABLE = new Array(ALPHABET_SIZE);
    for (let c = 0; c < ALPHABET_SIZE; c++) {
        DECRYPT_TABLE[c] = new Int8Array(ALPHABET_SIZE);
        for (let k = 0; k < ALPHABET_SIZE; k++) {
            let p = c - k;
            if (p < 0) p += ALPHABET_SIZE;
            DECRYPT_TABLE[c][k] = p;
        }
    }
    
    // Bigram scores (26x26)
    BIGRAM_TABLE = new Float32Array(676);
    const bigrams = {TH:2,HE:2,IN:2,ER:2,AN:2,RE:2,ND:2,AT:2,ON:2,NT:2,HA:2,ES:2,ST:2,EN:2,ED:2};
    for (const [bg, score] of Object.entries(bigrams)) {
        const idx = ALPHABET_MAP[bg[0]] * 26 + ALPHABET_MAP[bg[1]];
        BIGRAM_TABLE[idx] = score;
    }
    
    // Trigram scores (26x26x26 = 17576)
    TRIGRAM_TABLE = new Float32Array(17576);
    const trigrams = {THE:5,AND:5,ING:5,HER:5,HIS:5,THA:5,ERE:5,FOR:5,ENT:5,ION:5};
    for (const [tg, score] of Object.entries(trigrams)) {
        const idx = ALPHABET_MAP[tg[0]] * 676 + ALPHABET_MAP[tg[1]] * 26 + ALPHABET_MAP[tg[2]];
        TRIGRAM_TABLE[idx] = score;    }
}

// === PRECOMPUTE KEY POSITIONS (once per key) ===
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

// === PRECOMPUTE CIPHERTEXT POSITIONS (once per batch) ===
let CT_POS_CACHE = null;
function precomputeCiphertext(ct) {
    const len = ct.length;
    const pos = new Int8Array(len);
    for (let i = 0; i < len; i++) {
        pos[i] = ALPHABET_MAP[ct[i]];
        if (pos[i] === undefined) return null;
    }
    return pos;
}

// === ULTRA-FAST DECRYPT (uses precomputed tables) ===
function decryptFast(ctPos, keyPos, klen) {
    const len = ctPos.length;
    const result = new Int8Array(len);
    
    for (let i = 0; i < len; i++) {
        result[i] = DECRYPT_TABLE[ctPos[i]][keyPos[i % klen]];
    }
    
    return result;
}

// === FAST SCORE (uses lookup tables, no string ops in loop) ===
function scoreFast(plainPos, len) {
    if (len < 3) return 0;
    
    let score = 0;
    
    // Bigrams (single pass through lookup table)
    for (let i = 0; i < len - 1; i++) {
        const idx = plainPos[i] * 26 + plainPos[i + 1];
        score += BIGRAM_TABLE[idx];
    }    
    // Trigrams
    for (let i = 0; i < len - 2; i++) {
        const idx = plainPos[i] * 676 + plainPos[i + 1] * 26 + plainPos[i + 2];
        score += TRIGRAM_TABLE[idx];
    }
    
    // Known fragments (check once at end)
    if (KNOWN_REGEX && len >= 3) {
        let text = '';
        for (let i = 0; i < Math.min(200, len); i++) {
            text += ALPHABET[plainPos[i]];
        }
        const matches = text.match(KNOWN_REGEX);
        if (matches) {
            for (const m of matches) {
                score += 10 + m.length * 2;
            }
        }
    }
    
    // Normalize
    return score * Math.min(1, len / 100);
}

// === CONVERT POS TO STRING (only for results) ===
function posToString(pos) {
    let result = '';
    for (let i = 0; i < pos.length; i++) {
        result += ALPHABET[pos[i]];
    }
    return result;
}

// === SIMPLE TRANSFORMS (on position arrays) ===
function reverseSegmentPos(pos, start, end) {
    const result = pos.slice();
    for (let i = start, j = end - 1; i < j; i++, j--) {
        [result[i], result[j]] = [result[j], result[i]];
    }
    return result;
}

function shiftPos(pos, shift) {
    const result = new Int8Array(pos.length);
    for (let i = 0; i < pos.length; i++) {
        let v = pos[i] + shift;
        if (v < 0) v += ALPHABET_SIZE;
        result[i] = v % ALPHABET_SIZE;
    }    return result;
}

function transposePos(pos, width) {
    const len = pos.length;
    const rows = Math.ceil(len / width);
    const result = new Int8Array(len);
    let idx = 0;
    for (let c = 0; c < width; c++) {
        for (let r = 0; r < rows; r++) {
            const p = r * width + c;
            if (p < len) result[idx++] = pos[p];
        }
    }
    return result;
}

// === PATTERN DETECT (on position arrays) ===
function detectPatternsPos(pos, len) {
    const patterns = [];
    const scan = Math.min(64, len);
    
    for (let i = 0; i < scan - 3; i++) {
        if (pos[i] === pos[i+3] && pos[i+1] === pos[i+4]) {
            patterns.push({ type: 'repeat', pos: i });
            break;
        }
    }
    
    for (let i = 0; i < scan - 3; i++) {
        if (pos[i] === pos[i+3] && pos[i+1] === pos[i+2]) {
            patterns.push({ type: 'palindrome', pos: i, len: 4 });
            break;
        }
    }
    
    return patterns;
}

// === ATTACK VARIANTS (precompute once per key) ===
function getVariantData(ctPos, key) {
    const variants = [];
    
    // 1. Original
    variants.push({ ct: ctPos, key, attack: 'original' });
    
    // 2. Reverse ciphertext
    variants.push({ ct: ctPos.slice().reverse(), key, attack: 'reverse_ct' });
    
    // 3. Reversed key    variants.push({ ct: ctPos, key: key.split('').reverse().join(''), attack: 'key_reverse' });
    
    // 4-5. Alphabet shifts (will apply after decrypt)
    variants.push({ ct: ctPos, key, attack: 'alphabet_shift+1', shift: 1 });
    variants.push({ ct: ctPos, key, attack: 'alphabet_shift-1', shift: -1 });
    
    // 6. Transpose
    variants.push({ ct: transposePos(ctPos, 5), key, attack: 'transpose_5' });
    
    return variants;
}

// === CACHED CIPHERTEXT POSITIONS ===
let CACHED_CT_POS = null;
let CACHED_CT = '';

// === PROCESS BATCH ===
function processBatch(ciphertext, keys) {
    const results = [];
    const startTime = performance.now();
    const threshold = SCORE_THRESHOLD * 0.5;
    
    // Cache ciphertext positions if changed
    if (ciphertext !== CACHED_CT) {
        CACHED_CT = ciphertext;
        CACHED_CT_POS = precomputeCiphertext(ciphertext);
    }
    const ctPos = CACHED_CT_POS;
    
    if (!ctPos) {
        return { keysTested: keys.length, results: [], currentSpeed: 0 };
    }
    
    for (const key of keys) {
        const keyPos = precomputeKey(key);
        if (!keyPos) continue;
        const klen = keyPos.length;
        
        const variants = getVariantData(ctPos, key);
        
        for (const variant of variants) {
            const variantKeyPos = variant.key === key ? keyPos : precomputeKey(variant.key);
            if (!variantKeyPos) continue;
            
            // Decrypt
            const plainPos = decryptFast(variant.ct, variantKeyPos, variantKeyPos.length);
            
            // Handle alphabet shift variants
            let finalPos = plainPos;
            if (variant.shift) {                finalPos = shiftPos(plainPos, variant.shift);
            }
            
            // Score
            let baseScore = scoreFast(finalPos, finalPos.length);
            if (baseScore < threshold) continue;
            
            // Transforms only for good candidates
            let bestPos = finalPos;
            let bestScore = baseScore;
            let transforms = [];
            let patterns = [];
            
            const detected = detectPatternsPos(finalPos, finalPos.length);
            if (detected.length > 0 && baseScore < threshold * 3) {
                let current = finalPos;
                let currentScore = baseScore;
                
                for (const p of detected) {
                    if (transforms.length >= 2) break;
                    
                    if (p.type === 'palindrome') {
                        const transformed = reverseSegmentPos(current, p.pos, p.pos + 4);
                        const newScore = scoreFast(transformed, transformed.length);
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
                    } else if (p.type === 'repeat') {
                        const transformed = shiftPos(current, 1);
                        const newScore = scoreFast(transformed, transformed.length);
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
                    }
                }
            }            
            if (bestScore > threshold) {
                results.push({
                    key: variant.key,
                    plaintext: posToString(bestPos),
                    score: parseFloat(bestScore.toFixed(2)),
                    baseScore: parseFloat(baseScore.toFixed(2)),
                    transforms,
                    patterns,
                    attack: variant.attack,
                    attackDescription: variant.attack,
                    isSpecificKey: TEST_KEYS.length > 0 && keys.length === 0
                });
            }
        }
    }
    
    const elapsed = performance.now() - startTime;
    return {
        keysTested: keys.length,
        results,
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
        
        const knownFrags = (e.data.knownText || "").split(',').map(f => f.trim().toUpperCase()).filter(f => f);
        if (knownFrags.length > 0) {
            const escaped = knownFrags.map(f => f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'));
            KNOWN_REGEX = new RegExp('(' + escaped.join('|') + ')', 'gi');
        }
        
        initTables();
        CACHED_CT = CIPHERTEXT;
        CACHED_CT_POS = precomputeCiphertext(CIPHERTEXT);
        
        return;
    }

    if (e.data.type === 'process') {        const result = processBatch(e.data.ciphertext, e.data.keys);
        postMessage({
            keysTested: result.keysTested,
            results: result.results,
            currentSpeed: result.currentSpeed,
            workerId: WORKER_ID
        });
    }
};
