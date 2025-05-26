// Worker state
let ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
let ALPHABET_SIZE = 26;
let ALPHABET_POSITIONS = {};
let CIPHERTEXT_LENGTH = 0;
let KNOWN_TEXT = "";
let BATCH_SIZE = 100000;
let SCORE_THRESHOLD = 1.0;
let WORKER_ID = 0;

// Precomputed frequency data
const ENGLISH_FREQUENCIES = {
    'A': 8.167, 'B': 1.492, 'C': 2.782, 'D': 4.253,
    'E': 12.702, 'F': 2.228, 'G': 2.015, 'H': 6.094,
    'I': 6.966, 'J': 0.153, 'K': 0.772, 'L': 4.025,
    'M': 2.406, 'N': 6.749, 'O': 7.507, 'P': 1.929,
    'Q': 0.095, 'R': 5.987, 'S': 6.327, 'T': 9.056,
    'U': 2.758, 'V': 0.978, 'W': 2.360, 'X': 0.150,
    'Y': 1.974, 'Z': 0.074
};

// Common words dictionary (frequency sorted)
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

// Common bigrams (2-letter combinations)
const COMMON_BIGRAMS = [
    'TH', 'HE', 'IN', 'ER', 'AN', 'RE', 'ND', 'AT', 'ON', 'NT',
    'HA', 'ES', 'ST', 'EN', 'ED', 'TO', 'IT', 'OU', 'EA', 'HI',
    'IS', 'OR', 'TI', 'AS', 'TE', 'ET', 'NG', 'OF', 'AL', 'DE',
    'SE', 'LE', 'SA', 'SI', 'AR', 'VE', 'RA', 'LD', 'UR'
];

// Common trigrams (3-letter combinations)
const COMMON_TRIGRAMS = [
    'THE', 'AND', 'ING', 'HER', 'HAT', 'HIS', 'THA', 'ERE', 'FOR', 'ENT',
    'ION', 'TER', 'WAS', 'YOU', 'ITH', 'VER', 'ALL', 'WIT', 'THI', 'TIO'
];

// Initialize alphabet positions
function initAlphabetPositions() {
    ALPHABET_POSITIONS = {};
    for (let i = 0; i < ALPHABET.length; i++) {
        ALPHABET_POSITIONS[ALPHABET[i]] = i;
    }
}

// Optimized Vigenère decryption using precomputed positions
function vigenereDecrypt(ciphertext, key) {
    const keyLen = key.length;
    const plaintext = new Array(ciphertext.length);
    const keyPositions = new Array(keyLen);
    
    // Precompute key positions
    for (let i = 0; i < keyLen; i++) {
        keyPositions[i] = ALPHABET_POSITIONS[key[i]];
        if (keyPositions[i] === undefined) return ""; // Invalid key character
    }
    
    for (let i = 0; i < ciphertext.length; i++) {
        const cipherChar = ciphertext[i];
        const cipherPos = ALPHABET_POSITIONS[cipherChar];
        if (cipherPos === undefined) return ""; // Invalid ciphertext character
        
        // Vigenère decryption formula: P = (C - K) mod alphabet_size
        const keyPos = keyPositions[i % keyLen];
        let plainPos = (cipherPos - keyPos) % ALPHABET_SIZE;
        if (plainPos < 0) plainPos += ALPHABET_SIZE;
        
        plaintext[i] = ALPHABET[plainPos];
    }
    
    return plaintext.join('');
}

// Precompute word scores for faster matching
const WORD_SCORES = {};
COMMON_WORDS.forEach((word, index) => {
    // Longer words and more common words get higher scores
    WORD_SCORES[word] = 0.5 + (word.length * 0.3) + (index < 20 ? 0.5 : 0);
});

// More sophisticated scoring algorithm with optimizations
function scoreText(text, known) {
    if (!text || text.length === 0) return 0;
    
    let score = 0;
    const upperText = text.toUpperCase();
    const textLen = upperText.length;
    
    // 1. Check for common words (highest weight)
    for (const word in WORD_SCORES) {
        if (word.length > textLen) continue;
        
        let pos = 0;
        while ((pos = upperText.indexOf(word, pos)) !== -1) {
            score += WORD_SCORES[word];
            pos += word.length;
        }
    }
    
    // 2. Check known fragments (very high weight)
    if (known && known.trim() !== '') {
        const fragments = known.split(',').map(f => f.trim()).filter(f => f.length > 0);
        for (const fragment of fragments) {
            if (fragment.length > textLen) continue;
            
            let pos = 0;
            while ((pos = upperText.indexOf(fragment, pos)) !== -1) {
                // Known fragments are very important
                score += 5 + (fragment.length * 1.5);
                pos += fragment.length;
            }
        }
    }
    
    // 3. Check common trigrams (medium weight)
    for (const trigram of COMMON_TRIGRAMS) {
        if (trigram.length > textLen) continue;
        
        let pos = 0;
        while ((pos = upperText.indexOf(trigram, pos)) !== -1) {
            score += 0.3;
            pos += trigram.length;
        }
    }
    
    // 4. Check common bigrams (low weight)
    for (const bigram of COMMON_BIGRAMS) {
        if (bigram.length > textLen) continue;
        
        let pos = 0;
        while ((pos = upperText.indexOf(bigram, pos)) !== -1) {
            score += 0.1;
            pos += bigram.length;
        }
    }
    
    // 5. Letter frequency analysis
    const charCounts = {};
    let totalChars = 0;
    
    // Count character frequencies
    for (const char of upperText) {
        if (ALPHABET_POSITIONS[char] !== undefined) {
            charCounts[char] = (charCounts[char] || 0) + 1;
            totalChars++;
        }
    }
    
    // Compare to English frequencies
    if (totalChars > 0) {
        for (const char in ENGLISH_FREQUENCIES) {
            if (ALPHABET_POSITIONS[char] === undefined) continue;
            
            const expected = ENGLISH_FREQUENCIES[char] / 100; // Convert percentage to fraction
            const observed = (charCounts[char] || 0) / totalChars;
            const diff = Math.abs(expected - observed);
            
            // Higher score for better matches, with more weight to common letters
            score += (1 - diff) * expected * 15;
        }
    }
    
    // 6. Penalize for non-alphabetic characters (shouldn't exist in proper Vigenère)
    const nonAlpha = upperText.match(new RegExp(`[^${ALPHABET}]`, 'g'));
    if (nonAlpha) {
        score -= nonAlpha.length * 0.2;
    }
    
    // 7. Normalize score by text length (longer texts can have higher scores)
    if (textLen > 0) {
        score = score * (Math.min(textLen, 100) / 100);
    }
    
    return Math.max(0, score);
}

function processBatch(ciphertext, keys) {
    const results = [];
    const startTime = performance.now();
    const threshold = SCORE_THRESHOLD * 0.5; // Lower threshold for worker
    
    for (const key of keys) {
        const plaintext = vigenereDecrypt(ciphertext, key);
        if (!plaintext) continue;
        
        const score = scoreText(plaintext, KNOWN_TEXT);
        
        if (score > threshold) {
            results.push({
                key,
                plaintext,
                score: parseFloat(score.toFixed(2))
            });
        }
    }
    
    const batchTime = performance.now() - startTime;
    const currentSpeed = batchTime > 0 ? Math.round((keys.length / batchTime) * 1000) : 0;
    
    return {
        keysTested: keys.length,
        results,
        currentSpeed
    };
}

onmessage = function(e) {
    if (e.data.type === 'init') {
        // Initialize worker with parameters from main thread
        ALPHABET = e.data.alphabet || "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        ALPHABET_SIZE = ALPHABET.length;
        CIPHERTEXT_LENGTH = e.data.ciphertextLength || 0;
        KNOWN_TEXT = e.data.knownText || "";
        BATCH_SIZE = e.data.batchSize || 100000;
        SCORE_THRESHOLD = e.data.scoreThreshold || 1.0;
        WORKER_ID = e.data.workerId || 0;
        
        // Initialize alphabet positions
        initAlphabetPositions();
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
