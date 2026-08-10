import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk978A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581537672390402, 360581600950930996⟩, ⟨75686269426022697, 79865062951049427⟩, true⟩

def state01 : KState := ⟨⟨360570896135121602, 360570959427024693⟩, ⟨1116423250500340360, 1120603350946472486⟩, true⟩

def words00 : List Nat := [360582417559925893, 360582417519604485, 360582417401772441, 360582417231814502, 360582417061603958, 360582416849083267, 360582416688242694, 360582416598843205, 360582416509290487, 360582416367531252]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579490076979244, 360579553382320124⟩, ⟨275748294975935238, 279929709834803378⟩, true⟩

def words01 : List Nat := [360582416251566228, 360582416112079334, 360582415972141598, 360582415936943911, 360582415797431804, 360582415569328457, 360582415340958489, 360582415169591381, 360582415091864540, 360582415064080856]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360567914361893023, 360567977680765840⟩, ⟨1408035722409530772, 1412218461029286140⟩, true⟩

def words02 : List Nat := [360582415036105260, 360582414955811838, 360582414805917695, 360582414672474323, 360582414538685331, 360582414313460117, 360582414026741121, 360582413687792352, 360582413348577372, 360582413114283466]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560219116358006, 360560282448630435⟩, ⟨2160914804120209449, 2165098853690949065⟩, true⟩

def words03 : List Nat := [360582412967879560, 360582412860839081, 360582412753620856, 360582412594189334, 360582412418519629, 360582412181790468, 360582411944647586, 360582411792089116, 360582411647720478, 360582411423014031]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360606368145669255, 360606431491350349⟩, ⟨(-2354549519010010720), (-2350364157470213112)⟩, true⟩

def words04 : List Nat := [360582411197989692, 360582411077790611, 360582411073527096, 360582411124441261, 360582411125760587, 360582411071426267, 360582411138897650, 360582411225835507, 360582411416726825, 360582411663678990]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk978A
