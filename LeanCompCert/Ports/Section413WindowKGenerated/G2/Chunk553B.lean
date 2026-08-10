import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk553A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk553B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk553A

def state06 : KState := ⟨⟨360600302234444688, 360600321620611778⟩, ⟨(-1024392266619366074), (-1023667154755004812)⟩, true⟩

def words05 : List Nat := [360581826058855410, 360581826858248242, 360581827494736122, 360581828036937557, 360581828496881813, 360581828957028205, 360581829688881538, 360581830187651935, 360581830522365976, 360581830857172624]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608212793394320, 360608232186844019⟩, ⟨(-1462452812399723427), (-1461727297334233401)⟩, true⟩

def words06 : List Nat := [360581831179097660, 360581831664605369, 360581831979128479, 360581832293772696, 360581832330420338, 360581832377408638, 360581832522342027, 360581832667501081, 360581832921135774, 360581833398717848]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607861061005489, 360607880461787146⟩, ⟨(-1442934552578699680), (-1442208631506279388)⟩, true⟩

def words07 : List Nat := [360581833713475876, 360581834028306723, 360581834668322581, 360581835557745166, 360581836358631996, 360581837159614855, 360581837713082617, 360581837941790464, 360581838412664769, 360581838883781941]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360606707359068230, 360606726767104166⟩, ⟨(-1379072281180314880), (-1378345958330065652)⟩, true⟩

def words08 : List Nat := [360581839679872366, 360581840151299984, 360581840460041673, 360581840768871131, 360581840813494096, 360581841085144096, 360581841588269789, 360581842091525027, 360581842383595359, 360581842833643314]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360615662891347755, 360615682306666872⟩, ⟨(-1875331066707990004), (-1874604340406020908)⟩, true⟩

def words09 : List Nat := [360581843175781913, 360581843518123125, 360581843958400565, 360581844074123434, 360581844074840746, 360581843912422941, 360581843784318716, 360581844070973428, 360581844682395086, 360581845293970242]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk553B
