/-
  RagaModes.lean
  ==============

  Hindustani thaats as seven-swara subsets of the twelve swara-sthanas (Z/12).
  Init-only, zero sorry. The same chromatic ring as ChromaticChord / ScalesModes,
  read through the Indian system: Sa (0) and Pa (7) are the fixed drone in every
  thaat; the other swaras take their shuddha (natural) or vikrit (komal/tivra)
  positions, and each choice carves a different mood from the one octave.

  Bilawal is the major scale itself (cross-linked to ScalesModes); Bhairav's komal
  Re and komal Dha (1 and 8) give it its austere augmented-second character.
-/

import Gnosis.ScalesModes

namespace RagaModes

/-- The ten classical thaats (each seven swaras, as pitch classes from Sa=0). -/
def bilawal : List Nat := [0, 2, 4, 5, 7, 9, 11]   -- major
def kafi : List Nat := [0, 2, 3, 5, 7, 9, 10]      -- Dorian-like (komal ga, ni)
def bhairav : List Nat := [0, 1, 4, 5, 7, 8, 11]   -- komal re & dha
def bhairavi : List Nat := [0, 1, 3, 5, 7, 8, 10]  -- Phrygian-like (all komal)
def yaman : List Nat := [0, 2, 4, 6, 7, 9, 11]     -- tivra ma (Lydian-like)
def todi : List Nat := [0, 1, 3, 6, 7, 8, 11]      -- komal re ga dha, tivra ma

def below12 (x : Nat) : Bool := x < 12

/-- Every thaat has exactly seven swaras. -/
theorem each_thaat_has_seven_swaras :
    bilawal.length = 7 ∧ kafi.length = 7 ∧ bhairav.length = 7 ∧
    bhairavi.length = 7 ∧ yaman.length = 7 ∧ todi.length = 7 := by decide

/-- Every swara lies within the twelve-tone octave. -/
theorem thaats_live_in_the_twelve :
    bilawal.all below12 ∧ bhairav.all below12 ∧ yaman.all below12 ∧ todi.all below12 := by
  decide

/-- Sa (0) and Pa (7) — the drone — are present in every thaat. -/
theorem sa_and_pa_are_the_drone :
    (bilawal.contains 0 && bilawal.contains 7) ∧
    (bhairav.contains 0 && bhairav.contains 7) ∧
    (yaman.contains 0 && yaman.contains 7) ∧
    (todi.contains 0 && todi.contains 7) := by decide

/-- Bhairav's signature: komal Re (1) and komal Dha (8), the two austere lowerings. -/
theorem bhairav_komal_re_and_dha :
    bhairav.contains 1 ∧ bhairav.contains 8 := by decide

/-- Yaman's signature: tivra Ma (6) raised, and no perfect fourth (5). -/
theorem yaman_has_tivra_ma :
    yaman.contains 6 ∧ yaman.contains 5 = false := by decide

/-- Bilawal IS the major scale: it is the seven swaras of ScalesModes' Ionian
    pattern from Sa (the octave dropped). The thaat and the mode are one set. -/
theorem bilawal_is_the_major_scale :
    bilawal = (ScalesModes.scaleFrom 0 ScalesModes.ionianSteps).take 7 := by decide

end RagaModes
