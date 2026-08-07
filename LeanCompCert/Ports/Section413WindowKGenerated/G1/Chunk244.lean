import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk244

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477645552289222, 362477653659970989⟩, ⟨191104168360443244, 191237925136085284⟩, true⟩

def state01 : KState := ⟨⟨362479307086286649, 362479315200857642⟩, ⟨150759619628866963, 150893544537096003⟩, true⟩

def words00 : List Nat := [371285491739102623, 371285491949135972, 371285493347106078, 371285494745265443, 371285495901241309, 371285495902010306, 371285495420172368, 371285496020648269, 371285496828268941, 371285496829064816]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 24400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 24400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362511069956873125, 362511078078448336⟩, ⟨(-624700427515147811), (-624566331599044463)⟩, true⟩

def words01 : List Nat := [371285496576409228, 371285496296003155, 371285497415173720, 371285498188236337, 371285499338681646, 371285500489350160, 371285501645133172, 371285501645903306, 371285502060643632, 371285503108889390]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 24410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 24400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490680722278932, 362490688850714990⟩, ⟨(-126640828789002899), (-126506565295437071)⟩, true⟩

def words02 : List Nat := [371285505836978831, 371285506330207288, 371285506510682899, 371285506691399818, 371285507371758770, 371285507378269187, 371285508485047421, 371285509592038266, 371285510521402859, 371285510734170623]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 24420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 24400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362535458871269456, 362535467006667864⟩, ⟨(-1220822078459645899), (-1220687644840771289)⟩, true⟩

def words03 : List Nat := [371285511783850701, 371285512833848825, 371285515301420128, 371285516057284450, 371285516575801439, 371285517094502279, 371285518291680665, 371285518658575567, 371285520702811824, 371285522747233276]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 24430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 24400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362528640989364826, 362528649131715469⟩, ⟨(-1054204390560857727), (-1054069786993938691)⟩, true⟩

def words04 : List Nat := [371285524780713709, 371285525378442974, 371285527653052718, 371285529927889710, 371285532695892623, 371285533779767922, 371285534755178153, 371285535730778100, 371285537892104500, 371285539656152346]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 24440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 24400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492682508438264, 362492690657722397⟩, ⟨(-174804212441967819), (-174669439315008157)⟩, true⟩

def words05 : List Nat := [371285542112493328, 371285544568929501, 371285546753477263, 371285546754247813, 371285547058374510, 371285547407922223, 371285549062873947, 371285549340644396, 371285549633180465, 371285549925973286]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 24450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 24400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362528744178405885, 362528752334588406⟩, ⟨(-1056988884909732098), (-1056853943012693656)⟩, true⟩

def words06 : List Nat := [371285551592980060, 371285552446186285, 371285554324611751, 371285556203210153, 371285557613671186, 371285557614445742, 371285558585144247, 371285559732481563, 371285562552711049, 371285564318446332]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 24460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 24400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502594593364096, 362502602756600236⟩, ⟨(-416786286779917578), (-416651172247109948)⟩, true⟩

def words07 : List Nat := [371285566093869733, 371285567869426220, 371285571317541562, 371285573938007220, 371285576545580653, 371285579153224796, 371285581686634062, 371285581995569630, 371285582691397618, 371285583387610117]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 24470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 24400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362498891893316996, 362498900063419377⟩, ⟨(-326077886209349672), (-325942603555080472)⟩, true⟩

def words08 : List Nat := [371285585755583527, 371285585899712575, 371285586031854681, 371285586164238501, 371285586604362699, 371285586639029113, 371285588048958512, 371285589459092082, 371285590850551517, 371285591394783753]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 24480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 24400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362517600903464839, 362517609080551658⟩, ⟨(-784372223278615169), (-784236769540231307)⟩, true⟩

def words09 : List Nat := [371285593144240865, 371285594893948227, 371285597317614480, 371285597830712382, 371285597914816945, 371285597999163262, 371285598470711833, 371285598471570232, 371285599415613318, 371285600722952367]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 24490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 24400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 24400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk244
