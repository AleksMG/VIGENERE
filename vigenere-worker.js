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

// Precomputed tables
let DECRYPT_TABLE = null;
let BIGRAM_TABLE = null;
let TRIGRAM_TABLE = null;
let WORD_SCORES = {};

// Attack variants
let ATTACK_CT_VARIANTS = [];

// Initialize all tables
function initTables() {
    ALPHABET_MAP = {};
    for (let i = 0; i < ALPHABET_SIZE; i++) {
        ALPHABET_MAP[ALPHABET[i]] = i;
    }
    
    DECRYPT_TABLE = new Array(ALPHABET_SIZE);
    for (let c = 0; c < ALPHABET_SIZE; c++) {
        DECRYPT_TABLE[c] = new Int8Array(ALPHABET_SIZE);
        for (let k = 0; k < ALPHABET_SIZE; k++) {
            let p = c - k;
            if (p < 0) p += ALPHABET_SIZE;
            DECRYPT_TABLE[c][k] = p;
        }
    }
    
    BIGRAM_TABLE = new Float32Array(676);
    for (let i = 0; i < 676; i++) BIGRAM_TABLE[i] = 0.1;
    const bigrams = {'TH':3,'HE':3,'IN':3,'ER':3,'AN':3,'RE':3,'ND':3,'AT':3,'ON':3,'NT':3,'HA':2,'ES':2,'ST':2,'EN':2,'ED':2};
    for (const bg in bigrams) {
        if (ALPHABET_MAP[bg[0]] !== undefined && ALPHABET_MAP[bg[1]] !== undefined) {
            const idx = ALPHABET_MAP[bg[0]] * 26 + ALPHABET_MAP[bg[1]];
            BIGRAM_TABLE[idx] = bigrams[bg];
        }
    }
    
    TRIGRAM_TABLE = new Float32Array(17576);    for (let i = 0; i < 17576; i++) TRIGRAM_TABLE[i] = 0.2;
    const trigrams = {'THE':6,'AND':6,'ING':6,'HER':5,'HIS':5,'THA':5,'ERE':5,'FOR':5,'ENT':5,'ION':5};
    for (const tg in trigrams) {
        if (ALPHABET_MAP[tg[0]] !== undefined && ALPHABET_MAP[tg[1]] !== undefined && ALPHABET_MAP[tg[2]] !== undefined) {
            const idx = ALPHABET_MAP[tg[0]] * 676 + ALPHABET_MAP[tg[1]] * 26 + ALPHABET_MAP[tg[2]];
            TRIGRAM_TABLE[idx] = trigrams[tg];
        }
    }
    
    WORD_SCORES = {};
    const words = ['THE','BE','TO','OF','AND','A','IN','THAT','HAVE','I','IT','FOR','NOT','ON','WITH','HE','AS','YOU','DO','AT','BERLIN','EAST','NORTH','CLOCK'];
    for (let i = 0; i < words.length; i++) {
        WORD_SCORES[words[i]] = 1.0 + words[i].length * 0.5 + (i < 20 ? 3.0 : 0);
    }
}

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

function initAttackVariants(ctPos) {
    ATTACK_CT_VARIANTS = [];
    ATTACK_CT_VARIANTS.push({name: 'original', ctPos: ctPos, description: 'Standard Vigenère'});
    
    const revCt = new Int8Array(ctPos.length);
    for (let i = 0; i < ctPos.length; i++) revCt[i] = ctPos[ctPos.length - 1 - i];
    ATTACK_CT_VARIANTS.push({name: 'reverse_ct', ctPos: revCt, description: 'Reversed ciphertext'});
    
    ATTACK_CT_VARIANTS.push({name: 'transpose_5', ctPos: transposePos(ctPos, 5), description: 'Columnar transposition (5)'});    ATTACK_CT_VARIANTS.push({name: 'transpose_7', ctPos: transposePos(ctPos, 7), description: 'Columnar transposition (7)'});
    if (ctPos.length >= 10) {
        ATTACK_CT_VARIANTS.push({name: 'transpose_10', ctPos: transposePos(ctPos, 10), description: 'Columnar transposition (10)'});
    }
}

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

function decryptFast(ctPos, keyPos, klen) {
    const len = ctPos.length;
    const result = new Int8Array(len);
    for (let i = 0; i < len; i++) {
        result[i] = DECRYPT_TABLE[ctPos[i]][keyPos[i % klen]];
    }
    return result;
}

function scoreFast(plainPos, len) {
    if (len < 3) return 0;
    let score = 0;
    for (let i = 0; i < len - 1; i++) {
        const idx = plainPos[i] * 26 + plainPos[i + 1];
        score += BIGRAM_TABLE[idx];
    }
    for (let i = 0; i < len - 2; i++) {
        const idx = plainPos[i] * 676 + plainPos[i + 1] * 26 + plainPos[i + 2];
        score += TRIGRAM_TABLE[idx];
    }
    return score * Math.min(1.0, len / 100);
}

function checkKnown(plainPos, len) {
    if (!KNOWN_REGEX || len < 3) return 0;
    let text = '';
    const checkLen = Math.min(200, len);
    for (let i = 0; i < checkLen; i++) text += ALPHABET[plainPos[i]];
    const matches = text.match(KNOWN_REGEX);
    if (matches) {
        let bonus = 0;
        for (let m = 0; m < matches.length; m++) bonus += 10 + matches[m].length * 2;
        return bonus;    }
    return 0;
}

function checkWords(plainPos, len) {
    if (len < 3) return 0;
    let text = '';
    const checkLen = Math.min(200, len);
    for (let i = 0; i < checkLen; i++) text += ALPHABET[plainPos[i]];
    let bonus = 0;
    for (const word in WORD_SCORES) {
        if (text.indexOf(word) >= 0) bonus += WORD_SCORES[word];
    }
    return bonus;
}

function posToString(pos) {
    let result = '';
    for (let i = 0; i < pos.length; i++) result += ALPHABET[pos[i]];
    return result;
}

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

function detectPatternsPos(pos, len) {
    const patterns = [];
    const scan = Math.min(64, len);
    for (let i = 0; i < scan - 3; i++) {
        if (pos[i] === pos[i+3] && pos[i+1] === pos[i+4]) {
            patterns.push({type: 'repeat', pos: i});
            break;
        }    }
    for (let i = 0; i < scan - 3; i++) {
        if (pos[i] === pos[i+3] && pos[i+1] === pos[i+2]) {
            patterns.push({type: 'palindrome', pos: i, len: 4});
            break;
        }
    }
    return patterns;
}

function applyTransforms(plainPos, len, baseScore) {
    const threshold = SCORE_THRESHOLD * 0.5;
    if (baseScore < threshold) return {pos: plainPos, score: baseScore, transforms: [], patterns: []};
    
    let bestPos = plainPos;
    let bestScore = baseScore;
    let transforms = [];
    let patterns = [];
    
    const detected = detectPatternsPos(plainPos, len);
    if (detected.length === 0) return {pos: plainPos, score: baseScore, transforms: [], patterns: []};
    
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
                patterns.push('repeat');                if (currentScore > bestScore) {
                    bestPos = current;
                    bestScore = currentScore;
                }
            }
        }
    }
    
    return {pos: bestPos, score: bestScore, transforms: transforms, patterns: patterns};
}

function processBatch(ciphertext, keys) {
    const results = [];
    const startTime = performance.now();
    const threshold = SCORE_THRESHOLD * 0.5;
    const ctPos = CT_POS;
    
    if (!ctPos) {
        return {keysTested: keys.length, results: [], currentSpeed: 0};
    }
    
    for (let k = 0; k < keys.length; k++) {
        const key = keys[k];
        const keyPos = precomputeKey(key);
        if (!keyPos) continue;
        const klen = keyPos.length;
        
        for (let v = 0; v < ATTACK_CT_VARIANTS.length; v++) {
            const variant = ATTACK_CT_VARIANTS[v];
            const plainPos = decryptFast(variant.ctPos, keyPos, klen);
            
            let baseScore = scoreFast(plainPos, plainPos.length);
            baseScore += checkKnown(plainPos, plainPos.length);
            baseScore += checkWords(plainPos, plainPos.length);
            
            if (baseScore < threshold) continue;
            
            const transformed = applyTransforms(plainPos, plainPos.length, baseScore);
            
            if (transformed.score > threshold) {
                results.push({
                    key: key,
                    plaintext: posToString(transformed.pos),
                    score: parseFloat(transformed.score.toFixed(2)),
                    baseScore: parseFloat(baseScore.toFixed(2)),
                    transforms: transformed.transforms,
                    patterns: transformed.patterns,
                    attack: variant.name,
                    attackDescription: variant.description,
                    isSpecificKey: TEST_KEYS.length > 0 && keys.length === 0                });
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
            const escaped = knownFrags.map(function(f) { return f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'); });
            KNOWN_REGEX = new RegExp('(' + escaped.join('|') + ')', 'gi');
        }
        
        initTables();
        CT_POS = precomputeCT(CIPHERTEXT);
        if (CT_POS) initAttackVariants(CT_POS);
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
