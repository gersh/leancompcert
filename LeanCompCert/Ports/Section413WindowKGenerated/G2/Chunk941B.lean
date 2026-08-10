import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk941A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk941B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk941A

def state06 : KState := ⟨⟨360602228728363893, 360602287212210675⟩, ⟨(-1906508847342962467), (-1902790307549734571)⟩, true⟩

def words05 : List Nat := [360582077642055781, 360582077842232652, 360582078154741283, 360582078378385316, 360582078506194220, 360582078634106642, 360582078759137237, 360582078941672038, 360582079157395693, 360582079373428699]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593688030405742, 360593746527225993⟩, ⟨(-1102377530735119809), (-1098657769297300913)⟩, true⟩

def words06 : List Nat := [360582079532664048, 360582079656576330, 360582079770837984, 360582079885523622, 360582079947186812, 360582079948550568, 360582079919815740, 360582079835017106, 360582079776499874, 360582079901945416]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360572861331604096, 360572919841286266⟩, ⟨858934272893805070, 862655245602754736⟩, true⟩

def words07 : List Nat := [360582079968636194, 360582080035566750, 360582080045763842, 360582080047127694, 360582079944894941, 360582079814485663, 360582079683663371, 360582079620332225, 360582079580848848, 360582079485006831]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591395982270253, 360591454504821776⟩, ⟨(-886741404615272847), (-883019219808763385)⟩, true⟩

def words08 : List Nat := [360582079388853711, 360582079441477533, 360582079561465746, 360582079681710901, 360582079693987001, 360582079695350969, 360582079595092800, 360582079577674577, 360582079631132307, 360582079732074818]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579557152291343, 360579615687848862⟩, ⟨228428498829805080, 232151908736810702⟩, true⟩

def words09 : List Nat := [360582079776289882, 360582079820678046, 360582079881784550, 360582080000320673, 360582080090037262, 360582080179974693, 360582080191134920, 360582080192505573, 360582080170082873, 360582080145478765]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk941B
