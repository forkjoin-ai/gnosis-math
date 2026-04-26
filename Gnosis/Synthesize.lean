import Gnosis.GesturalCompiler

namespace Gnosis
namespace Articulatory

def trackEventToJson (e : TrackEvent Float) : String :=
  s!"\{\"value\": {e.value}, \"startTime\": {e.startTime}}"

def larynxEventToJson (e : TrackEvent LarynxState) : String :=
  s!"\{\"pitch\": {e.value.pitch}, \"pressure\": {e.value.pressure}, \"tension\": {e.value.tension}, \"isVoiced\": {if e.value.isVoiced then "true" else "false"}, \"startTime\": {e.startTime}}"

def listToJson {α} (l : List α) (f : α → String) : String :=
  "[" ++ String.intercalate ", " (l.map f) ++ "]"

def scoreToJson (s : GesturalScore) : String :=
  s!"\{ \"tongueHeight\": {listToJson s.tongueHeight trackEventToJson}, " ++
  s!"\"tongueBackness\": {listToJson s.tongueBackness trackEventToJson}, " ++
  s!"\"lipRounding\": {listToJson s.lipRounding trackEventToJson}, " ++
  s!"\"lipClosure\": {listToJson s.lipClosure trackEventToJson}, " ++
  s!"\"velumOpening\": {listToJson s.velumOpening trackEventToJson}, " ++
  s!"\"larynx\": {listToJson s.larynx larynxEventToJson} }"

def parsePhoneme (s : String) : Phoneme :=
  if s == "P" then Phoneme.P
  else if s == "B" then Phoneme.B
  else if s == "T" then Phoneme.T
  else if s == "D" then Phoneme.D
  else if s == "K" then Phoneme.K
  else if s == "G" then Phoneme.G
  else if s == "M" then Phoneme.M
  else if s == "N" then Phoneme.N
  else if s == "NG" then Phoneme.NG
  else if s == "S" then Phoneme.S
  else if s == "Z" then Phoneme.Z
  else if s == "SH" then Phoneme.SH
  else if s == "ZH" then Phoneme.ZH
  else if s == "CH" then Phoneme.CH
  else if s == "JH" then Phoneme.JH
  else if s == "F" then Phoneme.F
  else if s == "V" then Phoneme.V
  else if s == "TH" then Phoneme.TH
  else if s == "DH" then Phoneme.DH
  else if s == "HH" then Phoneme.HH
  else if s == "H" then Phoneme.HH
  else if s == "IY" then Phoneme.IY
  else if s == "IH" then Phoneme.IH
  else if s == "EH" then Phoneme.EH
  else if s == "AE" then Phoneme.AE
  else if s == "AA" then Phoneme.AA
  else if s == "AH" then Phoneme.AH
  else if s == "AO" then Phoneme.AO
  else if s == "OW" then Phoneme.OW
  else if s == "UH" then Phoneme.UH
  else if s == "UW" then Phoneme.UW
  else if s == "OY" then Phoneme.OY
  else if s == "AY" then Phoneme.AY
  else if s == "AW" then Phoneme.AW
  else if s == "EY" then Phoneme.EY
  else if s == "ER" then Phoneme.ER
  else if s == "L" then Phoneme.L
  else if s == "R" then Phoneme.R
  else if s == "W" then Phoneme.W
  else if s == "Y" then Phoneme.Y
  else if s == "SIL" then Phoneme.SIL
  else Phoneme.Other

def compileAndPrint (word : List Phoneme) : IO Unit :=
  let score := compileWord word
  IO.println (scoreToJson score)

end Articulatory
end Gnosis

def main (args : List String) : IO Unit := do
  if args.isEmpty then
    Gnosis.Articulatory.compileAndPrint [Gnosis.Articulatory.Phoneme.SIL]
  else
    let phonemes := args.map Gnosis.Articulatory.parsePhoneme
    Gnosis.Articulatory.compileAndPrint phonemes
