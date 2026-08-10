import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk277A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360486718075280622, 360486722658627218⟩, ⟨2655816261245805461, 2655902133394419981⟩, true⟩

def state01 : KState := ⟨⟨360577123220259580, 360577127807051257⟩, ⟨151191947584584373, 151277915178802941⟩, true⟩

def words00 : List Nat := [360582600141085385, 360582597978951896, 360582596602009279, 360582595602683108, 360582594603400573, 360582592491851235, 360582590431588629, 360582589298319323, 360582588165027136, 360582587132752405]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360518466516808654, 360518471107086008⟩, ⟨1776834690165279524, 1776920754364070712⟩, true⟩

def words01 : List Nat := [360582586936071341, 360582586084036028, 360582585231997722, 360582583938061892, 360582583424319419, 360582582193358635, 360582580962445027, 360582579079036064, 360582575899555051, 360582573587402173]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360478411551331614, 360478416145045309⟩, ⟨2887325578939340181, 2887411738410895587⟩, true⟩

def words02 : List Nat := [360582571275282416, 360582569515679612, 360582566869026723, 360582563570680705, 360582560272513116, 360582556643126776, 360582553668513512, 360582550087301656, 360582546506313078, 360582542064209063]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587111144527736, 360587115741687949⟩, ⟨(-127655098586144379), (-127568843525358319)⟩, true⟩

def words03 : List Nat := [360582538309650333, 360582534745303282, 360582531181106513, 360582528912535140, 360582526705356931, 360582523362268694, 360582520019351701, 360582517971799186, 360582517008665726, 360582517174818501]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610907285411961, 360610911886057358⟩, ⟨(-788111579127253675), (-788025227370331357)⟩, true⟩

def words04 : List Nat := [360582517175149675, 360582516341814321, 360582517102532707, 360582518130433682, 360582518587881566, 360582518588247145, 360582517751989994, 360582516263315140, 360582514774671497, 360582515603855984]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk277A
