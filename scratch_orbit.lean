import Init
import Gnosis.SpinorCover600Cell

set_option maxRecDepth 8000

open Cover ZPhi

-- left-mult orbit BFS
def stepOrbit (gens : List QZ) (seen : List QZ) : List QZ :=
  seen.foldl (fun acc a =>
    gens.foldl (fun acc2 g =>
      let p := qmulS g a
      if acc2.contains p then acc2 else acc2 ++ [p]) acc) seen

def iterOrbit (gens : List QZ) : Nat → List QZ → List QZ
  | 0, seen => seen
  | n+1, seen =>
    let nxt := stepOrbit gens seen
    if nxt.length == seen.length then seen else iterOrbit gens n nxt

def orbit : List QZ := iterOrbit gens2 200 [qOne]

#eval orbit.length
#eval (decide (orbit.length = 120) : Bool)
-- check it equals icosa as a set
#eval (orbit.all (fun a => icosa.contains a) : Bool)
#eval (icosa.all (fun a => orbit.contains a) : Bool)
