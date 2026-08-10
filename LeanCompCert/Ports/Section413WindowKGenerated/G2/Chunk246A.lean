import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk246A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk246A
