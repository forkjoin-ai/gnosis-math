import Gnosis.ArticulatorySynthesis
import Gnosis.Real

namespace Gnosis
namespace Articulatory

/-!
  # Gestural Compiler: Full Phonetic Lexicon
-/

def getGestures : Phoneme → PhonemeGestures
  | Phoneme.SIL => {
      tongueHeight   := { target := 0.0, dominance := 0.1 },
      tongueBackness := { target := 0.0, dominance := 0.1 },
      lipRounding    := { target := 0.0, dominance := 0.1 },
      lipClosure     := { target := 0.0, dominance := 0.1 },
      velumOpening   := { target := 0.0, dominance := 0.1 },
      larynx         := { pitch := 0.0, pressure := 0.0, tension := 0.0, isVoiced := false },
      duration       := 0.1
    }
  | Phoneme.M => {
      tongueHeight   := { target := 0.0, dominance := 0.0 },
      tongueBackness := { target := 0.0, dominance := 0.0 },
      lipRounding    := { target := 0.0, dominance := 0.2 },
      lipClosure     := { target := 1.0, dominance := 1.0 },
      velumOpening   := { target := 1.0, dominance := 1.0 },
      larynx         := defaultLarynx,
      duration       := 0.1
    }
  | Phoneme.B => {
      tongueHeight   := { target := 0.0, dominance := 0.0 },
      tongueBackness := { target := 0.0, dominance := 0.0 },
      lipRounding    := { target := 0.0, dominance := 0.2 },
      lipClosure     := { target := 1.0, dominance := 1.0 },
      velumOpening   := { target := 0.0, dominance := 1.0 },
      larynx         := defaultLarynx,
      duration       := 0.08
    }
  | Phoneme.AA => {
      tongueHeight   := { target := -0.8, dominance := 1.0 },
      tongueBackness := { target := 0.5,  dominance := 1.0 },
      lipRounding    := { target := 0.0,  dominance := 0.5 },
      lipClosure     := { target := 0.0,  dominance := 0.5 },
      velumOpening   := { target := 0.0,  dominance := 0.8 },
      larynx         := defaultLarynx,
      duration       := 0.15
    }
  | Phoneme.IY => {
      tongueHeight   := { target := 0.8,  dominance := 1.0 },
      tongueBackness := { target := -0.8, dominance := 1.0 },
      lipRounding    := { target := 0.0,  dominance := 0.5 },
      lipClosure     := { target := 0.0,  dominance := 0.5 },
      velumOpening   := { target := 0.0,  dominance := 1.0 },
      larynx         := defaultLarynx,
      duration       := 0.15
    }
  | Phoneme.S => {
      tongueHeight   := { target := 0.8,  dominance := 1.0 },
      tongueBackness := { target := -0.2, dominance := 0.8 },
      lipRounding    := { target := 0.0,  dominance := 0.0 },
      lipClosure     := { target := 0.0,  dominance := 0.5 },
      velumOpening   := { target := 0.0,  dominance := 1.0 },
      larynx         := { defaultLarynx with isVoiced := false, pressure := 0.8 },
      duration       := 0.12
    }
  | Phoneme.DH => { -- "The"
      tongueHeight   := { target := 0.5,  dominance := 1.0 },
      tongueBackness := { target := -0.5, dominance := 0.8 },
      lipRounding    := { target := 0.0,  dominance := 0.0 },
      lipClosure     := { target := 0.0,  dominance := 0.0 },
      velumOpening   := { target := 0.0,  dominance := 1.0 },
      larynx         := defaultLarynx,
      duration       := 0.08
    }
  | Phoneme.F => { -- "Of"
      tongueHeight   := { target := 0.0,  dominance := 0.0 },
      tongueBackness := { target := 0.0,  dominance := 0.0 },
      lipRounding    := { target := 0.0,  dominance := 0.0 },
      lipClosure     := { target := 0.5,  dominance := 1.0 },
      velumOpening   := { target := 0.0,  dominance := 1.0 },
      larynx         := { defaultLarynx with isVoiced := false, pressure := 0.7 },
      duration       := 0.1
    }
  | Phoneme.L => { -- "Light", "Clear"
      tongueHeight   := { target := 0.8,  dominance := 1.0 },
      tongueBackness := { target := 0.0,  dominance := 0.5 },
      lipRounding    := { target := 0.0,  dominance := 0.0 },
      lipClosure     := { target := 0.0,  dominance := 0.0 },
      velumOpening   := { target := 0.0,  dominance := 1.0 },
      larynx         := defaultLarynx,
      duration       := 0.1
    }
  | Phoneme.R => {
      tongueHeight   := { target := 0.3,  dominance := 1.0 },
      tongueBackness := { target := 0.8,  dominance := 0.8 },
      lipRounding    := { target := 0.5,  dominance := 0.8 },
      lipClosure     := { target := 0.0,  dominance := 0.0 },
      velumOpening   := { target := 0.0,  dominance := 1.0 },
      larynx         := defaultLarynx,
      duration       := 0.1
    }
  | Phoneme.AY => {
      tongueHeight   := { target := -0.8, dominance := 1.0 },
      tongueBackness := { target := 0.5,  dominance := 1.0 },
      lipRounding    := { target := 0.0,  dominance := 0.5 },
      lipClosure     := { target := 0.0,  dominance := 0.5 },
      velumOpening   := { target := 0.0,  dominance := 1.0 },
      larynx         := defaultLarynx,
      duration       := 0.15
    }
  | Phoneme.AE => {
      tongueHeight   := { target := -0.6, dominance := 1.0 },
      tongueBackness := { target := -0.6, dominance := 1.0 },
      lipRounding    := { target := 0.0,  dominance := 0.5 },
      lipClosure     := { target := 0.0,  dominance := 0.5 },
      velumOpening   := { target := 0.0,  dominance := 1.0 },
      larynx         := defaultLarynx,
      duration       := 0.15
    }
  | Phoneme.EH => {
      tongueHeight   := { target := 0.2, dominance := 1.0 },
      tongueBackness := { target := -0.4, dominance := 1.0 },
      lipRounding    := { target := 0.0,  dominance := 0.5 },
      lipClosure     := { target := 0.0,  dominance := 0.5 },
      velumOpening   := { target := 0.0,  dominance := 1.0 },
      larynx         := defaultLarynx,
      duration       := 0.12
    }
  | _ => {
      tongueHeight   := { target := 0.0, dominance := 0.5 },
      tongueBackness := { target := 0.0, dominance := 0.5 },
      lipRounding    := { target := 0.0, dominance := 0.5 },
      lipClosure     := { target := 0.0, dominance := 0.5 },
      velumOpening   := { target := 0.0, dominance := 0.5 },
      larynx         := defaultLarynx,
      duration       := 0.12
    }

def expandPhonemes (word : List Phoneme) : List PhonemeGestures :=
  match word with
  | [] => []
  | Phoneme.OY :: rest => 
      { getGestures Phoneme.AO with duration := 0.1 } :: 
      { getGestures Phoneme.IH with duration := 0.1 } :: 
      expandPhonemes rest
  | Phoneme.AY :: rest => 
      { getGestures Phoneme.AA with duration := 0.1 } :: 
      { getGestures Phoneme.IY with duration := 0.1 } :: 
      expandPhonemes rest
  | w :: rest => getGestures w :: expandPhonemes rest

def getBlendedTarget (cur : Gesture) (future : List PhonemeGestures) (getG : PhonemeGestures → Gesture) : Float :=
  let rec lookAhead (fs : List PhonemeGestures) : Option Gesture :=
    match fs with
    | [] => none
    | f :: rest =>
        let fg := getG f
        if fg.dominance > 0.1 then some fg
        else lookAhead rest
  
  match lookAhead future with
  | none => cur.target
  | some nextG =>
      let totalDom := cur.dominance + nextG.dominance
      if totalDom > 0.0 then
        (cur.target * cur.dominance + nextG.target * nextG.dominance) / totalDom
      else
        cur.target

def isVowel : Phoneme → Bool
  | Phoneme.IY | Phoneme.IH | Phoneme.EH | Phoneme.AE | Phoneme.AA | Phoneme.AH | Phoneme.AO | Phoneme.OW | Phoneme.UH | Phoneme.UW | Phoneme.OY | Phoneme.AY | Phoneme.AW | Phoneme.EY | Phoneme.ER => true
  | _ => false

/-- 
  Syllabic Siphon:
  Applies Prosodic Stress to the Vowel Nucleus.
-/
def applySyllabicStress (ps : List PhonemeGestures) (p : Phoneme) (pg : PhonemeGestures) : PhonemeGestures :=
  if isVowel p then
    -- Nucleus detected: Increase pressure and duration
    { pg with duration := pg.duration * 1.2,
              larynx   := { pg.larynx with pressure := pg.larynx.pressure * 1.3 } }
  else pg

def buildTrack (ps : List PhonemeGestures) (getG : PhonemeGestures → Gesture) : List (TrackEvent Float) :=
  let rec scan (l : List PhonemeGestures) (curTime : Float) : List (TrackEvent Float) :=
    match l with
    | [] => []
    | p :: rest =>
        let g := getG p
        let blended := getBlendedTarget g rest getG
        { value := blended, startTime := curTime } :: scan rest (curTime + p.duration)
  scan ps 0.0

/-- 
  The Cognitive Gestural Compiler:
  Translates a phoneme sequence into a coordinated, blended physical score.
  Implements Syllabic Nucleus Stress and Phrase-Final Lengthening.
-/
def compileWord (word : List Phoneme) : GesturalScore :=
  let expanded := expandPhonemes word
  let stressedPgs := (word.zip expanded).map (λ (p, pg) => applySyllabicStress expanded p pg)
  
  -- Phrase-Final Lengthening: The last non-SIL phoneme is elongated.
  let pgs := 
    let rec elongate (l : List PhonemeGestures) : List PhonemeGestures :=
      match l with
      | [] => []
      | [p] => [p] -- SIL
      | [p1, p2] => -- p2 is SIL
          [{ p1 with duration := p1.duration * 1.6 }, p2]
      | p :: rest => p :: elongate rest
    elongate stressedPgs

  let rec buildLarynx (ps : List PhonemeGestures) (curTime : Float) : List (TrackEvent LarynxState) :=
    match ps with
    | [] => []
    | p :: rest => { value := p.larynx, startTime := curTime } :: buildLarynx rest (curTime + p.duration)

  { tongueHeight   := buildTrack pgs (·.tongueHeight),
    tongueBackness := buildTrack pgs (·.tongueBackness),
    lipRounding    := buildTrack pgs (·.lipRounding),
    lipClosure     := buildTrack pgs (·.lipClosure),
    velumOpening   := buildTrack pgs (·.velumOpening),
    larynx         := buildLarynx pgs 0.0 }

end Articulatory
end Gnosis