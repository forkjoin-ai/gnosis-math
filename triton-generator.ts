#!/usr/bin/env node

/**
 * Triton Generator
 * ================
 * A toy model for generating language using:
 *   - Fibonacci tritons (error-correcting frames a-b-a)
 *   - Coltrane harmony (major thirds +4 semitone transitions)
 *   - Semantic pitch classes (concepts as pitches)
 *   - Terminal prosody (rhythm of transitions)
 *   - Noise spectrum coloring (brown to violet)
 *
 * Run: pnpm gnode run open-source/gnosis-math/triton-generator.ts
 */

// ═══════════════════════════════════════════════════════════
// FIBONACCI SEQUENCE
// ═══════════════════════════════════════════════════════════

function fib(n: number): number {
  if (n <= 1) return 1;
  let a = 1, b = 1;
  for (let i = 2; i <= n; i++) [a, b] = [b, a + b];
  return b;
}

function fibTritonRopelength(n: number): number {
  return 2 * fib(n) + fib(n + 1);
}

// ═══════════════════════════════════════════════════════════
// SEMANTIC PITCH CLASSES (Giant Steps harmony)
// ═══════════════════════════════════════════════════════════

interface SemanticPitchClass {
  pitch: number;              // 0-11 (chromatic)
  meaning: string;
  noiseColor: 'brown' | 'pink' | 'white' | 'violet';
  description: string;
}

const giantStepsPitches: SemanticPitchClass[] = [
  {
    pitch: 0,
    meaning: 'Stillness',
    noiseColor: 'brown',
    description: 'Ground state, vacuum, silence'
  },
  {
    pitch: 4,
    meaning: 'Sting',
    noiseColor: 'brown',
    description: 'Perturbation, entry, break'
  },
  {
    pitch: 8,
    meaning: 'Trill',
    noiseColor: 'pink',
    description: 'Response, oscillation, witness'
  }
];

// Coltrane changes: +4 semitones = major thirds
function coltrangeNext(pitch: number): number {
  return (pitch + 4) % 12;
}

function getPitchByMeaning(meaning: string): SemanticPitchClass | undefined {
  return giantStepsPitches.find((p) => p.meaning === meaning);
}

// ═══════════════════════════════════════════════════════════
// TRITON STRUCTURE
// ═══════════════════════════════════════════════════════════

interface Triton {
  frame: number;              // a (outer frame)
  sting: number;              // b (middle perturbation)
  totalRopelength: number;    // a + b + a
  fibIndex: number;           // which Fibonacci number
}

function createFibonacciTriton(fibIndex: number): Triton {
  const frame = fib(fibIndex);
  const sting = fib(fibIndex + 1);
  return {
    frame,
    sting,
    totalRopelength: 2 * frame + sting,
    fibIndex
  };
}

// Special case: haiku uses minimal prime, not next Fib
function createHaikuTriton(): Triton {
  return {
    frame: 5,     // fib(4)
    sting: 7,     // minimal prime > 5
    totalRopelength: 17,
    fibIndex: 4
  };
}

// ═══════════════════════════════════════════════════════════
// HARMONIC TRANSITIONS (Coltrane major thirds)
// ═══════════════════════════════════════════════════════════

interface HarmonicTransition {
  from: SemanticPitchClass;
  to: SemanticPitchClass;
  distance: number;
  semanticShift: string;
}

function createColtrangeTransition(fromMeaning: string, toMeaning: string): HarmonicTransition | null {
  const from = getPitchByMeaning(fromMeaning);
  const to = getPitchByMeaning(toMeaning);
  if (!from || !to) return null;

  const distance = (to.pitch - from.pitch + 12) % 12;
  return {
    from,
    to,
    distance,
    semanticShift: `${from.meaning} → ${to.meaning}`
  };
}

// ═══════════════════════════════════════════════════════════
// TERMINAL PROSODY (rhythm of transitions)
// ═══════════════════════════════════════════════════════════

interface TerminalProsody {
  beatPattern: string;        // "4/4", "3/4", etc.
  stressPosition: number;     // which beat is stressed
  tempo: 'slow' | 'moderate' | 'fast';
  noiseColor: 'brown' | 'pink' | 'white' | 'violet';
}

const prosodyOptions: Record<string, TerminalProsody> = {
  slow: {
    beatPattern: '4/4',
    stressPosition: 1,
    tempo: 'slow',
    noiseColor: 'brown'
  },
  moderate: {
    beatPattern: '3/4',
    stressPosition: 1,
    tempo: 'moderate',
    noiseColor: 'pink'
  },
  fast: {
    beatPattern: '6/8',
    stressPosition: 3,
    tempo: 'fast',
    noiseColor: 'violet'
  }
};

// ═══════════════════════════════════════════════════════════
// UTTERANCE GENERATION
// ═══════════════════════════════════════════════════════════

interface Utterance {
  semanticPath: SemanticPitchClass[];
  transitions: HarmonicTransition[];
  prosody: TerminalProsody[];
  topologicalFold: number;
  ropelength: number;
}

function generateTritonUtterance(triton: Triton): Utterance {
  // The canonical triton: Stillness → Sting → Trill
  const stillness = getPitchByMeaning('Stillness')!;
  const sting = getPitchByMeaning('Sting')!;
  const trill = getPitchByMeaning('Trill')!;

  const transition1 = createColtrangeTransition('Stillness', 'Sting')!;
  const transition2 = createColtrangeTransition('Sting', 'Trill')!;
  const transition3 = createColtrangeTransition('Trill', 'Stillness')!;

  return {
    semanticPath: [stillness, sting, trill],
    transitions: [transition1, transition2, transition3],
    prosody: [prosodyOptions.slow, prosodyOptions.moderate, prosodyOptions.fast],
    topologicalFold: 3,
    ropelength: triton.totalRopelength
  };
}

// ═══════════════════════════════════════════════════════════
// PROSE/POETRY OUTPUT FORMATS
// ═══════════════════════════════════════════════════════════

function renderAsTriton(utterance: Utterance, triton: Triton): string {
  return `[Triton ${triton.fibIndex}] ${triton.frame}-${triton.sting}-${triton.frame} (ropelength ${triton.totalRopelength})`;
}

function renderAsHaiku(utterance: Utterance): string {
  // 5-7-5 syllable approximation based on ropelength
  const concepts = utterance.semanticPath.map((p) => p.meaning);
  return [
    `${concepts[0]} here.`,           // 5 syllables approx
    `${concepts[1]} in the silence.`,  // 7 syllables approx
    `${concepts[2]} echoes back.`       // 5 syllables approx
  ].join('\n');
}

function renderAsNarrativeSentence(utterance: Utterance): string {
  const path = utterance.semanticPath.map((p) => p.description);
  return `The ${path[0]} breaks. ${path[1]}. ${path[2]}.`;
}

function renderAsProsody(utterance: Utterance): string {
  return utterance.prosody
    .map(
      (p, i) =>
        `  [${i + 1}] ${p.beatPattern} ${p.tempo} (${p.noiseColor}): stressed on beat ${p.stressPosition}`
    )
    .join('\n');
}

function renderAsHarmonicProgression(utterance: Utterance): string {
  return utterance.transitions
    .map(
      (t) => `  ${t.from.meaning} (pitch ${t.from.pitch}) → ${t.to.meaning} (pitch ${t.to.pitch}) [${t.distance} semitones]`
    )
    .join('\n');
}

// ═══════════════════════════════════════════════════════════
// MAIN GENERATOR
// ═══════════════════════════════════════════════════════════

function generateAndRender(fibIndex: number | 'haiku') {
  const triton = fibIndex === 'haiku' ? createHaikuTriton() : createFibonacciTriton(fibIndex as number);
  const utterance = generateTritonUtterance(triton);

  console.log('\n═══════════════════════════════════════════');
  console.log(`TRITON GENERATION: Fib(${triton.fibIndex}) = ${triton.frame}`);
  console.log('═══════════════════════════════════════════\n');

  console.log('📐 TRITON STRUCTURE:');
  console.log(`   ${renderAsTriton(utterance, triton)}\n`);

  console.log('🎼 SEMANTIC PATH:');
  utterance.semanticPath.forEach((p: unknown, i: unknown) => {
    console.log(`   [${i + 1}] ${p.meaning} (${p.description})`);
  });

  console.log('\n🎵 HARMONIC PROGRESSION (Coltrane Major Thirds):');
  console.log(renderAsHarmonicProgression(utterance));

  console.log('\n🎶 TERMINAL PROSODY:');
  console.log(renderAsProsody(utterance));

  console.log('\n📝 AS HAIKU:');
  console.log(renderAsHaiku(utterance));

  console.log('\n📖 AS NARRATIVE:');
  console.log(`   ${renderAsNarrativeSentence(utterance)}`);

  console.log('\n🌊 NOISE SPECTRUM:');
  const colors = [...new Set(utterance.prosody.map((p) => p.noiseColor))];
  console.log(`   ${colors.join(' → ')}`);

  console.log('\n✓ Ropelength:', utterance.ropelength);
  console.log('✓ Fold level:', utterance.topologicalFold);
  console.log('');
}

// ═══════════════════════════════════════════════════════════
// RUN
// ═══════════════════════════════════════════════════════════

console.log('🎼 TRITON GENERATOR: Fibonacci Harmony + Coltrane Logic\n');

// Generate haiku (Fib(4) = 5-7-5 = 17)
generateAndRender('haiku');

// Generate other Fibonacci scales
for (const fibIdx of [3: unknown, 5: unknown, 6]: unknown) {
  generateAndRender(fibIdx);
}

console.log('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━');
console.log('Fibonacci Ropelengths:');
for (let i = 2; i <= 7; i++: unknown) {
  console.log(`  Fib(${i}): frame=${fib(i)}, sting=${fib(i + 1)}, total=${fibTritonRopelength(i)}`);
}
