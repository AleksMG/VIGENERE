// === HIGH-PERFORMANCE VIGENÈRE WORKER ===
// Оптимизации: early-exit, typed arrays, minimal allocations, precomputed tables

let ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
let ALPHABET_SIZE = 26;
let POS_ARRAY = new Int8Array(256); // -1 = invalid
let CIPHERTEXT = "";
let CT_CODES = null; // Uint8Array с кодами символов
let KNOWN_FRAGMENTS = [];
let BATCH_SIZE = 100000;
let SCORE_THRESHOLD = 1.0;
let WORKER_ID = 0;
let TEST_KEYS = [];

// === PRECOMPUTED TABLES ===
const BIGRAM_SCORES = new Float32Array(676); // 26*26
const TRIGRAM_SCORES = new Float32Array(17576); // 26^3
const WORD_SCORES = new Map();

// === INIT TABLES (вызывается один раз) ===
function initTables() {
    // POS_ARRAY
    POS_ARRAY.fill(-1);
    for (let i = 0; i < ALPHABET.length; i++) {
        POS_ARRAY[ALPHABET.charCodeAt(i)] = i;
    }
    
    // BIGRAM_SCORES (упрощённая эвристика)
    const commonBigrams = ['TH','HE','IN','ER','AN','RE','ND','AT','ON','NT','HA','ES','ST','EN','ED'];
    for (let i = 0; i < 676; i++) {
        const c1 = String.fromCharCode(65 + Math.floor(i / 26));
        const c2 = String.fromCharCode(65 + (i % 26));
        const bg = c1 + c2;
        BIGRAM_SCORES[i] = commonBigrams.includes(bg) ? 2.0 : 0.1;
    }
    
    // TRIGRAM_SCORES
    const commonTrigrams = ['THE','AND','ING','HER','HIS','THA','ERE','FOR','ENT','ION'];
    for (let i = 0; i < 17576; i++) {
        const c1 = String.fromCharCode(65 + Math.floor(i / 676));
        const c2 = String.fromCharCode(65 + Math.floor((i % 676) / 26));
        const c3 = String.fromCharCode(65 + (i % 26));
        const tg = c1 + c2 + c3;
        TRIGRAM_SCORES[i] = commonTrigrams.includes(tg) ? 5.0 : 0.2;
    }
    
    // WORD_SCORES
    const words = ['THE','BE','TO','OF','AND','A','IN','THAT','HAVE','I','IT','FOR','NOT','ON','WITH','HE','AS','YOU','DO','AT'];
    words.forEach((w, idx) => WORD_SCORES.set(w, 1.0 + w.length * 0.5 + (idx < 10 ? 2.0 : 0)));
}
// === FAST DECRYPT (ключевой оптимизированный путь) ===
function decryptFast(ctCodes, keyCodes, outBuffer) {
    const len = ctCodes.length;
    const klen = keyCodes.length;
    
    for (let i = 0; i < len; i++) {
        const cp = ctCodes[i];
        const kp = keyCodes[i % klen];
        if (cp < 0 || kp < 0) return -1; // invalid char
        
        let pp = cp - kp;
        if (pp < 0) pp += ALPHABET_SIZE;
        outBuffer[i] = pp;
    }
    return len;
}

// === ULTRA-FAST SCORING (early-exit, integer math) ===
function scoreFast(plainCodes, len) {
    if (len < 3) return 0;
    
    let score = 0;
    
    // 1. Known fragments (O(1) check per fragment)
    for (const frag of KNOWN_FRAGMENTS) {
        if (frag.length > len) continue;
        const fragCodes = frag.split('').map(c => POS_ARRAY[c.charCodeAt(0)]);
        if (fragCodes.includes(-1)) continue;
        
        // Boyer-Moore-lite search
        for (let i = 0; i <= len - frag.length; i++) {
            let match = true;
            for (let j = 0; j < frag.length; j++) {
                if (plainCodes[i + j] !== fragCodes[j]) { match = false; break; }
            }
            if (match) {
                score += 10 + frag.length * 2;
                break; // один раз на фрагмент
            }
        }
    }
    
    // Early exit: если уже хороший скор — возвращаем
    if (score > SCORE_THRESHOLD * 3) return score;
    
    // 2. Bigrams (однопроходный)
    for (let i = 0; i < len - 1; i++) {
        const idx = plainCodes[i] * 26 + plainCodes[i + 1];
        score += BIGRAM_SCORES[idx];    }
    
    // Early exit
    if (score > SCORE_THRESHOLD * 2) return score;
    
    // 3. Trigrams (только если текст длинный)
    if (len >= 3) {
        for (let i = 0; i < len - 2; i++) {
            const idx = plainCodes[i] * 676 + plainCodes[i+1] * 26 + plainCodes[i+2];
            score += TRIGRAM_SCORES[idx];
        }
    }
    
    // 4. Words (только топ-10 самых частых)
    const text = String.fromCharCode(...plainCodes.slice(0, Math.min(200, len)));
    for (const [word, pts] of WORD_SCORES) {
        if (text.includes(word)) score += pts;
    }
    
    // Normalize
    return score * Math.min(1, len / 100);
}

// === PATTERN DETECTION (только для топ-кандидатов) ===
function detectPatterns(plainCodes, len) {
    const patterns = [];
    const scanLen = Math.min(64, len);
    
    // Quick palindrome check (4-char)
    for (let i = 0; i < scanLen - 3; i++) {
        if (plainCodes[i] === plainCodes[i+3] && plainCodes[i+1] === plainCodes[i+2]) {
            patterns.push('PAL');
            break;
        }
    }
    
    // Quick repeat check
    for (let i = 0; i < scanLen - 3; i++) {
        if (plainCodes[i] === plainCodes[i+3] && plainCodes[i+1] === plainCodes[i+4]) {
            patterns.push('RPT');
            break;
        }
    }
    
    return patterns;
}

// === TEXT TRANSFORMS (применяются к кодам, не к строкам) ===
function transformReverseSegment(codes, start, end) {
    const result = codes.slice();    for (let i = start, j = end - 1; i < j; i++, j--) {
        [result[i], result[j]] = [result[j], result[i]];
    }
    return result;
}

function transformShiftText(codes, shift) {
    const result = new Int8Array(codes.length);
    for (let i = 0; i < codes.length; i++) {
        let v = codes[i] + shift;
        if (v < 0) v += ALPHABET_SIZE;
        result[i] = v % ALPHABET_SIZE;
    }
    return result;
}

// === ATTACK VARIANTS (6 векторов, но без лишних аллокаций) ===
function* getVariants(ctCodes, key) {
    // 1. Original
    yield { ct: ctCodes, key, alphabet: POS_ARRAY, attack: 'original' };
    
    // 2. Reverse ciphertext
    const revCt = ctCodes.slice().reverse();
    yield { ct: revCt, key, alphabet: POS_ARRAY, attack: 'reverse_ct' };
    
    // 3. Reversed key
    const revKey = key.split('').reverse().join('');
    yield { ct: ctCodes, key: revKey, alphabet: POS_ARRAY, attack: 'key_reverse' };
    
    // 4-5. Alphabet shifts (только если стандартный алфавит)
    if (ALPHABET_SIZE === 26) {
        const shiftPos = new Int8Array(256);
        shiftPos.fill(-1);
        const shifted = ALPHABET.slice(1) + ALPHABET[0];
        for (let i = 0; i < 26; i++) shiftPos[shifted.charCodeAt(i)] = i;
        yield { ct: ctCodes, key, alphabet: shiftPos, attack: 'alphabet_shift+1' };
        
        const shiftNeg = new Int8Array(256);
        shiftNeg.fill(-1);
        const shifted2 = ALPHABET[25] + ALPHABET.slice(0, 25);
        for (let i = 0; i < 26; i++) shiftNeg[shifted2.charCodeAt(i)] = i;
        yield { ct: ctCodes, key, alphabet: shiftNeg, attack: 'alphabet_shift-1' };
    }
    
    // 6. Transpose columns (width=5)
    const transposed = transposeCodes(ctCodes, 5);
    yield { ct: transposed, key, alphabet: POS_ARRAY, attack: 'transpose_5' };
}

function transposeCodes(codes, width) {    const len = codes.length;
    const rows = Math.ceil(len / width);
    const result = new Int8Array(len);
    let idx = 0;
    for (let c = 0; c < width; c++) {
        for (let r = 0; r < rows; r++) {
            const pos = r * width + c;
            if (pos < len) result[idx++] = codes[pos];
        }
    }
    return result;
}

// === MAIN PROCESS (оптимизированный цикл) ===
function processBatch(ctCodes, keys) {
    const results = [];
    const startTime = performance.now();
    const threshold = SCORE_THRESHOLD * 0.5;
    const outBuffer = new Int8Array(ctCodes.length);
    
    for (const key of keys) {
        const keyCodes = key.split('').map(c => POS_ARRAY[c.charCodeAt(0)]);
        if (keyCodes.includes(-1)) continue;
        
        for (const variant of getVariants(ctCodes, key)) {
            const plainLen = decryptFast(variant.ct, keyCodes, outBuffer);
            if (plainLen < 1) continue;
            
            // Быстрый скор
            let score = scoreFast(outBuffer, plainLen);
            if (score < threshold) continue;
            
            // Только для хороших кандидатов: паттерны + трансформации
            let bestCodes = outBuffer.slice();
            let bestScore = score;
            let transforms = [];
            
            const patterns = detectPatterns(bestCodes, plainLen);
            if (patterns.length > 0 && score < threshold * 3) {
                let current = bestCodes;
                let currentScore = score;
                
                for (const p of patterns) {
                    if (transforms.length >= 2) break;
                    
                    if (p === 'PAL') {
                        // Найти позицию палиндрома
                        for (let i = 0; i < Math.min(64, plainLen) - 3; i++) {
                            if (current[i] === current[i+3] && current[i+1] === current[i+2]) {
                                const transformed = transformReverseSegment(current, i, i + 4);                                const newScore = scoreFast(transformed, plainLen);
                                if (newScore > currentScore + 1.0) {
                                    current = transformed;
                                    currentScore = newScore;
                                    transforms.push('REV[PAL]');
                                    if (currentScore > bestScore) {
                                        bestCodes = current;
                                        bestScore = currentScore;
                                    }
                                }
                                break;
                            }
                        }
                    } else if (p === 'RPT') {
                        const shifted = transformShiftText(current, 1);
                        const newScore = scoreFast(shifted, plainLen);
                        if (newScore > currentScore + 1.0) {
                            current = shifted;
                            currentScore = newScore;
                            transforms.push('SHIFT[RPT]');
                            if (currentScore > bestScore) {
                                bestCodes = current;
                                bestScore = currentScore;
                            }
                        }
                    }
                }
            }
            
            if (bestScore > threshold) {
                // Конвертируем коды в строку только для результатов
                const plaintext = String.fromCharCode(...bestCodes.map(c => ALPHABET.charCodeAt(c)));
                results.push({
                    key: variant.key,
                    plaintext,
                    score: parseFloat(bestScore.toFixed(2)),
                    baseScore: parseFloat(score.toFixed(2)),
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
        keysTested: keys.length,        results,
        currentSpeed: elapsed > 0 ? Math.round((keys.length / elapsed) * 1000) : 0
    };
}

// === MESSAGE HANDLER ===
onmessage = function(e) {
    if (e.data.type === 'init') {
        ALPHABET = e.data.alphabet || "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        ALPHABET_SIZE = ALPHABET.length;
        CIPHERTEXT = e.data.ciphertext || "";
        KNOWN_FRAGMENTS = (e.data.knownText || "").split(',').map(f => f.trim().toUpperCase()).filter(f => f);
        BATCH_SIZE = e.data.batchSize || 100000;
        SCORE_THRESHOLD = e.data.scoreThreshold || 1.0;
        WORKER_ID = e.data.workerId || 0;
        TEST_KEYS = e.data.testSpecificKeys || [];
        
        // Precompute
        initTables();
        CT_CODES = new Int8Array(CIPHERTEXT.length);
        for (let i = 0; i < CIPHERTEXT.length; i++) {
            CT_CODES[i] = POS_ARRAY[CIPHERTEXT.charCodeAt(i)];
        }
        return;
    }

    if (e.data.type === 'process') {
        const ct = e.data.ciphertext ? 
            new Int8Array(e.data.ciphertext.length).map((_, i) => POS_ARRAY[e.data.ciphertext.charCodeAt(i)]) : 
            CT_CODES;
        const result = processBatch(ct, e.data.keys);
        postMessage({
            keysTested: result.keysTested,
            results: result.results,
            currentSpeed: result.currentSpeed,
            workerId: WORKER_ID
        });
    }
};
