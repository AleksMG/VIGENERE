// === VIGENÈRE K4 WORKER - OPTIMIZED ===
// Генерация ключей ВНУТРИ воркера = максимальная скорость

let ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
let ALPHABET_SIZE = 26;
let ALPHABET_POS_ARRAY = new Uint8Array(256);
let CIPHERTEXT = "";
let CIPHERTEXT_LENGTH = 0;
let KNOWN_FRAGMENTS = [];
let SCORE_THRESHOLD = 1.0;
let MIN_KEY_LENGTH = 3;
let MAX_KEY_LENGTH = 8;
let BATCH_SIZE = 50000;
let WORKER_ID = 0;
let TEST_SPECIFIC_KEYS = [];
let ENABLE_K4_MODE = false;
let ENABLE_AUTO_TRANSFORM = true;
let TRANSPOSITION_WIDTHS = [4, 5, 6, 7, 8];
let ATTACK_VARIANTS = {};

let STOP_FLAG = false;
let CURRENT_KEY_INDEX = 0;
let TOTAL_KEYS = 0;

const ENGLISH_FREQ = new Float32Array([8.167, 1.492, 2.782, 4.253, 12.702, 2.228, 2.015, 6.094, 6.966, 0.153, 0.772, 4.025, 2.406, 6.749, 7.507, 1.929, 0.095, 5.987, 6.327, 9.056, 2.758, 0.978, 2.360, 0.150, 1.974, 0.074]);

const BIGRAMS = new Set(['TH','HE','IN','ER','AN','RE','ND','AT','ON','NT','HA','ES','ST','EN','ED','TO','IT','OU','EA','HI']);
const TRIGRAMS = new Set(['THE','AND','ING','HER','HIS','THA','ERE','FOR','ENT','ION','TER','WAS','YOU','ITH','VER','ALL']);

function initAlphabetPositions() {
    ALPHABET_POS_ARRAY.fill(255);
    for (let i = 0; i < ALPHABET.length; i++) {
        ALPHABET_POS_ARRAY[ALPHABET.charCodeAt(i)] = i;
    }
    ALPHABET_SIZE = ALPHABET.length;
}

function compileKnownFragments() {
    KNOWN_FRAGMENTS = [];
    if (KNOWN_TEXT && KNOWN_TEXT.trim() !== '') {
        KNOWN_FRAGMENTS = KNOWN_TEXT.split(',').map(f => f.trim().toUpperCase()).filter(f => f.length > 0);
    }
}

// ✅ БЫСТРАЯ генерация ключа по индексу
function generateKey(index, length) {
    let key = "";
    let remaining = index;
    for (let i = 0; i < length; i++) {
        key = ALPHABET.charAt(remaining % ALPHABET_SIZE) + key;        remaining = Math.floor(remaining / ALPHABET_SIZE);
    }
    return key;
}

// ✅ БЫСТРЫЙ Vigenère decrypt с Uint8Array
function vigenereDecrypt(ciphertext, key) {
    const keyLen = key.length;
    const plaintext = new Array(ciphertext.length);
    const keyPositions = new Uint8Array(keyLen);
    
    for (let i = 0; i < keyLen; i++) {
        keyPositions[i] = ALPHABET_POS_ARRAY[key.charCodeAt(i)];
    }
    
    for (let i = 0; i < ciphertext.length; i++) {
        const cipherPos = ALPHABET_POS_ARRAY[ciphertext.charCodeAt(i)];
        if (cipherPos === 255) {
            plaintext[i] = ciphertext[i];
            continue;
        }
        let plainPos = cipherPos - keyPositions[i % keyLen];
        if (plainPos < 0) plainPos += ALPHABET_SIZE;
        plaintext[i] = ALPHABET[plainPos];
    }
    
    return plaintext.join('');
}

// ✅ БЫСТРЫЙ scoring - один проход
function scoreText(text) {
    if (!text || text.length === 0) return 0;
    
    let score = 0;
    const upperText = text.toUpperCase();
    const textLen = upperText.length;
    
    // Known fragments - высокий приоритет
    for (const frag of KNOWN_FRAGMENTS) {
        if (frag.length < 2) continue;
        let pos = 0;
        while ((pos = upperText.indexOf(frag, pos)) !== -1) {
            score += 50 * frag.length;
            pos += frag.length;
        }
    }
    
    // Trigrams - один проход
    for (let i = 0; i <= textLen - 3; i++) {
        const tri = upperText.slice(i, i + 3);        if (TRIGRAMS.has(tri)) score += 0.5;
    }
    
    // Bigrams - один проход
    for (let i = 0; i <= textLen - 2; i++) {
        const bi = upperText.slice(i, i + 2);
        if (BIGRAMS.has(bi)) score += 0.15;
    }
    
    // Frequency - один проход
    const charCounts = new Uint16Array(ALPHABET_SIZE);
    let totalChars = 0;
    for (let i = 0; i < textLen; i++) {
        const pos = ALPHABET_POS_ARRAY[upperText.charCodeAt(i)];
        if (pos !== 255) { charCounts[pos]++; totalChars++; }
    }
    
    if (totalChars > 0) {
        for (let i = 0; i < ALPHABET_SIZE; i++) {
            const expected = ENGLISH_FREQ[i] / 100;
            if (expected === 0) continue;
            const observed = charCounts[i] / totalChars;
            const diff = Math.abs(expected - observed);
            score += (1 - diff) * expected * 15;
        }
    }
    
    return score * Math.min(textLen, 100) / 100;
}

// ✅ Извлечение позиций фрагментов для подсветки
function extractFragmentMatches(text) {
    const matches = [];
    if (!KNOWN_FRAGMENTS.length) return matches;
    
    const upperText = text.toUpperCase();
    for (const frag of KNOWN_FRAGMENTS) {
        let pos = 0;
        while ((pos = upperText.indexOf(frag, pos)) !== -1) {
            matches.push({ start: pos, end: pos + frag.length, text: frag, type: 'full' });
            pos += frag.length;
        }
    }
    return matches;
}

// ✅ Транспозиция колонок
function transposeColumns(text, width) {
    if (!text || text.length === 0) return text;
    const rows = Math.ceil(text.length / width);    const grid = [];
    for (let r = 0; r < rows; r++) {
        grid.push(text.slice(r * width, (r + 1) * width).padEnd(width, ' '));
    }
    let result = '';
    for (let c = 0; c < width; c++) {
        for (let r = 0; r < rows; r++) result += grid[r][c];
    }
    return result.trim();
}

// ✅ Варианты атак
function getAttackVariants(ciphertext, key) {
    const variants = [];
    variants.push({ text: ciphertext, attack: 'original', key, description: 'Standard Vigenère' });
    
    if (ATTACK_VARIANTS.tryReverseCT) {
        variants.push({ text: ciphertext.split('').reverse().join(''), attack: 'reverse_ct', key, description: 'Reversed CT' });
    }
    if (ATTACK_VARIANTS.tryReverseKey) {
        variants.push({ text: ciphertext, attack: 'key_reverse', key: key.split('').reverse().join(''), description: 'Reversed Key' });
    }
    if (ATTACK_VARIANTS.tryAlphabetShift && ALPHABET_SIZE === 26) {
        variants.push({ text: ciphertext, attack: 'alphabet_shift+1', key, customAlphabet: ALPHABET.slice(1) + ALPHABET[0], description: 'Alpha +1' });
        variants.push({ text: ciphertext, attack: 'alphabet_shift-1', key, customAlphabet: ALPHABET[ALPHABET.length - 1] + ALPHABET.slice(0, -1), description: 'Alpha -1' });
    }
    
    // K4: транспозиции
    if (ENABLE_K4_MODE) {
        for (const w of TRANSPOSITION_WIDTHS.slice(0, 3)) {
            variants.push({ text: transposeColumns(ciphertext, w), attack: `transpose_${w}`, key, description: `Transpose ${w}` });
        }
    }
    
    return variants;
}

// ✅ Обработка батча - генерация ключей ВНУТРИ воркера
function processBatch() {
    const results = [];
    const startTime = performance.now();
    const threshold = SCORE_THRESHOLD * 0.5;
    let keysTested = 0;
    
    // Специфичные ключи
    if (TEST_SPECIFIC_KEYS.length > 0) {
        for (const testKey of TEST_SPECIFIC_KEYS) {
            const variants = getAttackVariants(CIPHERTEXT, testKey);
            for (const variant of variants) {
                let decryptAlphabet = ALPHABET;                if (variant.customAlphabet) {
                    decryptAlphabet = variant.customAlphabet;
                }
                
                const plaintext = vigenereDecrypt(variant.text, variant.key);
                if (!plaintext) continue;
                
                const baseScore = scoreText(plaintext);
                const fragmentMatches = extractFragmentMatches(plaintext);
                
                if (baseScore > threshold) {
                    results.push({
                        key: testKey,
                        plaintext: plaintext,
                        score: parseFloat(baseScore.toFixed(2)),
                        baseScore: parseFloat(baseScore.toFixed(2)),
                        transforms: [],
                        patterns: [],
                        attack: variant.attack,
                        attackDescription: variant.description,
                        fragmentMatches: fragmentMatches,
                        isSpecificKey: true
                    });
                }
            }
            keysTested++;
        }
    }
    
    // Брутфорс - генерация ключей внутри воркера
    const endTime = performance.now();
    const batchTime = endTime - startTime;
    
    return {
        keysTested: keysTested,
        results: results,
        currentSpeed: batchTime > 0 ? Math.round((keysTested / batchTime) * 1000) : 0
    };
}

// ✅ Главный цикл - генерация и тестирование ключей
function runBruteForce() {
    const results = [];
    const startTime = performance.now();
    const threshold = SCORE_THRESHOLD * 0.5;
    let keysTested = 0;
    const maxKeysPerBatch = BATCH_SIZE;
    
    // Определяем текущую длину ключа
    let currentLength = MIN_KEY_LENGTH;    let keysAtCurrentLength = Math.pow(ALPHABET_SIZE, currentLength);
    
    // Пропускаем уже обработанные
    while (CURRENT_KEY_INDEX >= keysAtCurrentLength && currentLength < MAX_KEY_LENGTH) {
        CURRENT_KEY_INDEX -= keysAtCurrentLength;
        currentLength++;
        keysAtCurrentLength = Math.pow(ALPHABET_SIZE, currentLength);
    }
    
    if (currentLength > MAX_KEY_LENGTH) {
        // Завершено
        postMessage({ keysTested: 0, results: [], currentSpeed: 0, workerId: WORKER_ID, done: true });
        return;
    }
    
    // Генерируем и тестируем ключи
    for (let i = 0; i < maxKeysPerBatch && currentLength <= MAX_KEY_LENGTH; i++) {
        if (CURRENT_KEY_INDEX >= keysAtCurrentLength) {
            CURRENT_KEY_INDEX = 0;
            currentLength++;
            if (currentLength > MAX_KEY_LENGTH) break;
            keysAtCurrentLength = Math.pow(ALPHABET_SIZE, currentLength);
        }
        
        const key = generateKey(CURRENT_KEY_INDEX, currentLength);
        CURRENT_KEY_INDEX++;
        
        const variants = getAttackVariants(CIPHERTEXT, key);
        for (const variant of variants) {
            const plaintext = vigenereDecrypt(variant.text, variant.key);
            if (!plaintext) continue;
            
            const baseScore = scoreText(plaintext);
            
            if (baseScore > threshold) {
                const fragmentMatches = extractFragmentMatches(plaintext);
                results.push({
                    key: variant.key,
                    plaintext: plaintext,
                    score: parseFloat(baseScore.toFixed(2)),
                    baseScore: parseFloat(baseScore.toFixed(2)),
                    transforms: [],
                    patterns: [],
                    attack: variant.attack,
                    attackDescription: variant.description,
                    fragmentMatches: fragmentMatches,
                    isSpecificKey: false,
                    autoDetected: variant.attack.includes('transpose')
                });
            }        }
        keysTested++;
    }
    
    const endTime = performance.now();
    const batchTime = endTime - startTime;
    
    postMessage({
        keysTested: keysTested,
        results: results,
        currentSpeed: batchTime > 0 ? Math.round((keysTested / batchTime) * 1000) : 0,
        workerId: WORKER_ID,
        done: currentLength > MAX_KEY_LENGTH
    });
}

onmessage = function(e) {
    if (e.data.type === 'init') {
        ALPHABET = e.data.alphabet || "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        ALPHABET_SIZE = ALPHABET.length;
        CIPHERTEXT = e.data.ciphertext || "";
        CIPHERTEXT_LENGTH = CIPHERTEXT.length;
        KNOWN_TEXT = e.data.knownText || "";
        MIN_KEY_LENGTH = e.data.minKeyLength || 3;
        MAX_KEY_LENGTH = e.data.maxKeyLength || 8;
        BATCH_SIZE = e.data.batchSize || 50000;
        SCORE_THRESHOLD = e.data.scoreThreshold || 1.0;
        WORKER_ID = e.data.workerId || 0;
        TEST_SPECIFIC_KEYS = e.data.testSpecificKeys || [];
        ENABLE_K4_MODE = e.data.enableK4Mode || false;
        ENABLE_AUTO_TRANSFORM = e.data.enableAutoTransform || true;
        TRANSPOSITION_WIDTHS = e.data.transpositionWidths || [4, 5, 6, 7, 8];
        ATTACK_VARIANTS = e.data.attackVariants || {};
        CURRENT_KEY_INDEX = WORKER_ID; // Распределяем по воркерам
        
        initAlphabetPositions();
        compileKnownFragments();
        
        // Сразу начинаем работу после init
        setTimeout(() => runBruteForce(), 10);
        return;
    }

    if (e.data.type === 'process') {
        runBruteForce();
    }
    
    if (e.data.type === 'stop') {
        STOP_FLAG = true;
    }};
