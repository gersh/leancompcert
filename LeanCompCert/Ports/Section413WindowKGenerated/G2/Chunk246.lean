import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk246

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360597109031219236, 360597112608858267⟩, ⟨(-333969305288727817), (-333909765675303691)⟩, true⟩

def state01 : KState := ⟨⟨360548374071926028, 360548377652586482⟩, ⟨865050362101937702, 865109976057632834⟩, true⟩

def words00 : List Nat := [360583541281290302, 360583541329863725, 360583541330149778, 360583540368055529, 360583539405992675, 360583537002659598, 360583535447933962, 360583534125630724, 360583532803401355, 360583530435034984]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 24600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 24600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360618206495936082, 360618210079631165⟩, ⟨(-853824793545270852), (-853765104892128482)⟩, true⟩

def words01 : List Nat := [360583529227880947, 360583529449144778, 360583530833705934, 360583531294120778, 360583531294419587, 360583530310118182, 360583529501587738, 360583530965142937, 360583532373982302, 360583533782775143]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 24610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 24600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360632960263108787, 360632963849863183⟩, ⟨(-1217345899430203549), (-1217286135441394171)⟩, true⟩

def words02 : List Nat := [360583534194957299, 360583534195280081, 360583535753364171, 360583537356198105, 360583538493723353, 360583539673585908, 360583540019674635, 360583540365770389, 360583540945094349, 360583542951992963]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 24620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 24600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560858578949522, 360560862168735266⟩, ⟨559055871538340522, 559115710204551208⟩, true⟩

def words03 : List Nat := [360583546604848200, 360583550257468153, 360583552379698849, 360583553307290723, 360583553308759138, 360583553310310966, 360583554399880829, 360583554473404760, 360583554473691388, 360583553553077984]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 24630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 24600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614128612484041, 360614132205304099⟩, ⟨(-753823281339139694), (-753763367892778414)⟩, true⟩

def words04 : List Nat := [360583552632459147, 360583553673952721, 360583555421118765, 360583557168203884, 360583557518137315, 360583557518459004, 360583556234873070, 360583554876914167, 360583553569355447, 360583554810152066]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 24640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 24600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360613618103828856, 360613621699713267⟩, ⟨(-741270803097967106), (-741210814100185594)⟩, true⟩

def words05 : List Nat := [360583554810443550, 360583554791823914, 360583555933394720, 360583558400881418, 360583560441891052, 360583562482787957, 360583563692351142, 360583563692672923, 360583564488714872, 360583565707900276]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604452252109384, 360604455851028599⟩, ⟨(-515274204208876341), (-515214140357336453)⟩, true⟩

def words06 : List Nat := [360583566210506274, 360583567374593932, 360583567708039928, 360583568041493951, 360583568041763511, 360583568677166594, 360583569928483117, 360583571179764392, 360583571613145568, 360583572459988215]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360660783075824437, 360660786677782270⟩, ⟨(-1905182564714907603), (-1905122425885775179)⟩, true⟩

def words07 : List Nat := [360583574947010320, 360583577433924725, 360583580154896021, 360583582641101762, 360583583597786838, 360583584554414269, 360583587150436772, 360583590582293858, 360583593710435880, 360583596838396274]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360651773192514197, 360651776797543325⟩, ⟨(-1682812193944043222), (-1682751979300380116)⟩, true⟩

def words08 : List Nat := [360583598961045783, 360583601844910517, 360583606367559233, 360583610889938710, 360583614987347342, 360583617455570980, 360583618853214000, 360583620250774939, 360583621593478504, 360583624354171231]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360599759339381343, 360599762947445083⟩, ⟨(-398172781164560138), (-398112491581042686)⟩, true⟩

def words09 : List Nat := [360583628752462932, 360583633150459846, 360583636719520916, 360583638660046336, 360583639527209399, 360583640394394817, 360583642898674098, 360583644379609335, 360583645032470120, 360583645685326908]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk246
