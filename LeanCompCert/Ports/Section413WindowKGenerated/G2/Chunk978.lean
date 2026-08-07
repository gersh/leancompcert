import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk978

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

def state06 : KState := ⟨⟨360599187370957028, 360599250730188088⟩, ⟨(-1651901736975915374), (-1647715049506310870)⟩, true⟩

def words05 : List Nat := [360582411843391287, 360582412023252890, 360582412198621640, 360582412437319980, 360582412649220582, 360582412861358583, 360582413013813882, 360582413082926913, 360582413256134039, 360582413429838549]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580604576739433, 360580667949350626⟩, ⟨166739377669642428, 170927374586499984⟩, true⟩

def words06 : List Nat := [360582413707404576, 360582413901288799, 360582414042677840, 360582414184226056, 360582414255098492, 360582414379154289, 360582414421508464, 360582414464105423, 360582414465377807, 360582414422984902]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360610637187400152, 360610700573422364⟩, ⟨(-2772718083614063335), (-2768528774093736025)⟩, true⟩

def words07 : List Nat := [360582414492786913, 360582414580849389, 360582414744829695, 360582414911233710, 360582414986342875, 360582415061544817, 360582415167367863, 360582415353604205, 360582415643731624, 360582415934175792]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602191049522163, 360602254449105126⟩, ⟨(-1946040604158145380), (-1941849967245838368)⟩, true⟩

def words08 : List Nat := [360582416138229169, 360582416258929717, 360582416483670509, 360582416708839071, 360582416907222214, 360582417070086735, 360582417170926622, 360582417271949591, 360582417385801711, 360582417590075738]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583135703011425, 360583199115965512⟩, ⟨(-80590176604656473), (-76398230724895575)⟩, true⟩

def words09 : List Nat := [360582417866248912, 360582418142688822, 360582418357777768, 360582418468991620, 360582418509033077, 360582418549430167, 360582418673490993, 360582418735165100, 360582418744402810, 360582418753857619]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk978
