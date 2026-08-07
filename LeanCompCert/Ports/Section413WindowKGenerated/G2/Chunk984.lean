import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk984

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571409428534579, 360571473516171846⟩, ⟨1074262394523695857, 1078520560676287471⟩, true⟩

def state01 : KState := ⟨⟨360578675862120513, 360578739963219835⟩, ⟨359146704748986567, 363406195634844109⟩, true⟩

def words00 : List Nat := [360582433980746638, 360582433916173265, 360582433748489013, 360582433529227994, 360582433309738005, 360582433064484045, 360582432918800148, 360582432876584191, 360582432834213071, 360582432740332272]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579591111332673, 360579655225941346⟩, ⟨269038716805362172, 273299537211299208⟩, true⟩

def words01 : List Nat := [360582432769623601, 360582432836857935, 360582432859300810, 360582432860730510, 360582432780387664, 360582432612415583, 360582432444182474, 360582432252796576, 360582432122562886, 360582432095858145]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565261516943123, 360565325645166016⟩, ⟨1679308287226693475, 1683570447610193605⟩, true⟩

def words02 : List Nat := [360582432068917970, 360582431983735260, 360582431795356986, 360582431610490644, 360582431425236479, 360582431192090776, 360582430902748848, 360582430529544716, 360582430156064357, 360582429886226772]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560621092355890, 360560685234040841⟩, ⟨2136154039560233905, 2140417525081743335⟩, true⟩

def words03 : List Nat := [360582429713613838, 360582429626986977, 360582429540217730, 360582429401906726, 360582429289027132, 360582429150361610, 360582429011271327, 360582428956750185, 360582428825291364, 360582428605892546]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567568104884334, 360567632260091729⟩, ⟨1452235728460126142, 1456500545198605640⟩, true⟩

def words04 : List Nat := [360582428386192472, 360582428138323332, 360582427941981965, 360582427849039473, 360582427755987667, 360582427575424744, 360582427291718512, 360582427043566257, 360582426794977016, 360582426577462970]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360568934850923267, 360568999019742903⟩, ⟨1317663078218955009, 1321929235149882041⟩, true⟩

def words05 : List Nat := [360582426428478260, 360582426227965497, 360582426027182569, 360582425929923421, 360582425894898160, 360582425767396800, 360582425639741482, 360582425446333283, 360582425208034059, 360582425073319482]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 98450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 98400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576139790252195, 360576203972562763⟩, ⟨608216551572472638, 612484036887960300⟩, true⟩

def words06 : List Nat := [360582424938124594, 360582424819035658, 360582424744769120, 360582424603594770, 360582424462186355, 360582424278838927, 360582424146517846, 360582424117549278, 360582424088460692, 360582423979030601]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 98460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 98400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593478700956870, 360593542896770929⟩, ⟨(-1099250514123380044), (-1094981699052183884)⟩, true⟩

def words07 : List Nat := [360582423924723956, 360582423934013759, 360582424045935357, 360582424088040977, 360582424089368398, 360582424039272710, 360582423988881631, 360582423958125959, 360582424072188003, 360582424186572493]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 98470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 98400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580258104135507, 360580322313596656⟩, ⟨202655073306895270, 206925232408511800⟩, true⟩

def words08 : List Nat := [360582424228738229, 360582424230169708, 360582424211847172, 360582424140257346, 360582424068288136, 360582423970394778, 360582423824063938, 360582423618576462, 360582423412812055, 360582423290674619]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 98480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 98400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575206640486321, 360575270863415949⟩, ⟨700260588034118400, 704532073714760008⟩, true⟩

def words09 : List Nat := [360582423352199087, 360582423435327871, 360582423466636102, 360582423510949200, 360582423528873255, 360582423547196303, 360582423562693366, 360582423564128314, 360582423544434088, 360582423473301379]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 98490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 98400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 98400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk984
