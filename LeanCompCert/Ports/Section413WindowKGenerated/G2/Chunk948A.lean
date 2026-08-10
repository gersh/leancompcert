import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk948A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360597625495378230, 360597684808195444⟩, ⟨(-1479166459462323433), (-1475369598266338371)⟩, true⟩

def state01 : KState := ⟨⟨360588154495697887, 360588213821472705⟩, ⟨(-581329232701390773), (-577531143061207127)⟩, true⟩

def words00 : List Nat := [360582122133494757, 360582122178050767, 360582122179274498, 360582122167947078, 360582122156395782, 360582122124621323, 360582122237094700, 360582122349853103, 360582122361940985, 360582122427614807]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360608432089951070, 360608491428678438⟩, ⟨(-2503977216535188339), (-2500177898799289687)⟩, true⟩

def words01 : List Nat := [360582122604183169, 360582122781151476, 360582123033494766, 360582123175228611, 360582123210141645, 360582123245125883, 360582123357843501, 360582123526255075, 360582123805449300, 360582124084959228]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360608144161073040, 360608203512900581⟩, ⟨(-2476663766030790069), (-2472863206073372687)⟩, true⟩

def words02 : List Nat := [360582124308401059, 360582124579639389, 360582124961758906, 360582125344289693, 360582125698316589, 360582126014712833, 360582126269898619, 360582126525229120, 360582126708567799, 360582126985118808]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577004877695308, 360577064242454991⟩, ⟨476432092290404738, 480233878668944206⟩, true⟩

def words03 : List Nat := [360582127240822833, 360582127496776909, 360582127680889866, 360582127754318716, 360582127766442340, 360582127778951234, 360582127902184096, 360582127914864229, 360582127916088503, 360582127864119573]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603376879007662, 360603436256764115⟩, ⟨(-2024858167610299545), (-2021055148554659211)⟩, true⟩

def words04 : List Nat := [360582127869599306, 360582128011818571, 360582128105777092, 360582128199974822, 360582128201242257, 360582128201343608, 360582128162033176, 360582128198918165, 360582128346526509, 360582128572622096]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk948A
